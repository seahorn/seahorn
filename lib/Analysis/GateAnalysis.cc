#include "seahorn/Analysis/GateAnalysis.hh"

#include "llvm/Pass.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"

#include "llvm/Analysis/PostDominators.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SparseBitVector.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "avy/AvyDebug.h"

#define GSA_LOG(...) LOG("gsa", __VA_ARGS__)

static llvm::cl::opt<bool>
    GsaDumpAfter("gsa-dump-after",
                 llvm::cl::desc("Dump function after running"),
                 llvm::cl::init(false));

using namespace llvm;

namespace seahorn {

namespace {

class GateAnalysisImpl : public seahorn::GateAnalysis {
  Function &m_function;
  DominatorTree &m_DT;
  PostDominatorTree &m_PDT;

  DenseMap<BasicBlock *, unsigned> m_BBToIdx;
  DenseMap<BasicBlock *, SparseBitVector<>> m_reach;

  DenseMap<std::pair<PHINode *, unsigned short>, Gate> m_gates;
  DenseMap<std::pair<SwitchInst *, BasicBlock *>, Value *> m_switchConditions;
  DenseMap<BranchInst *, Value *> m_negBranchConditions;

public:
  GateAnalysisImpl(Function &f, DominatorTree &dt, PostDominatorTree &pdt)
      : m_function(f), m_DT(dt), m_PDT(pdt) {
    initReach();
    calculate();

    if (GsaDumpAfter) {
      errs() << "Dumping IR after running Gated SSA analysis pass on function: "
             << f.getName() << "\n==========================================\n";
      f.print(errs());
      errs() << "\n";
    }
  }

  Gate getGatingCondition(PHINode *PN, size_t incomingArcIndex) const override;

private:
  void calculate();
  void initReach();
  void processSwitch(SwitchInst *SI);
  void processPhi(PHINode *PN);
  BasicBlock *getGatingBlock(PHINode *PN, BasicBlock *incomingBB);
  Value *getReachingCmp(BasicBlock *destBB, BasicBlock *incomingBB,
                        TerminatorInst *terminator);
  bool flowsTo(BasicBlock *src, BasicBlock *succ, BasicBlock *incoming,
               BasicBlock *dest);
};

Value *GetCondition(TerminatorInst *TI) {
  if (auto *BI = dyn_cast<BranchInst>(TI)) {
    assert(BI->isConditional() && "Unconditional branches cannot be gates!");
    return BI->getCondition();
  }

  if (auto *SI = dyn_cast<SwitchInst>(TI)) {
    assert(SI->getNumCases() > 1 && "Unconditional branches cannot be gates!");
    return SI->getCondition();
  }

  llvm_unreachable("Unhandled (or wrong) termiantor instruction");
}

void GateAnalysisImpl::calculate() {
  std::vector<PHINode *> phis;

  for (auto &BB : m_function) {
    for (auto &I : BB) {
      if (auto *PN = dyn_cast<PHINode>(&I)) {
        phis.push_back(PN);
      }
    }

    if (auto *SI = dyn_cast<SwitchInst>(BB.getTerminator()))
      processSwitch(SI);
  }

  for (PHINode *PN : phis)
    processPhi(PN);
}

void GateAnalysisImpl::initReach() {
  unsigned i = 0;
  for (auto &BB : m_function) {
    m_BBToIdx[&BB] = i;
    m_reach[&BB].set(i);
    ++i;
  }

  std::vector<SmallDenseSet<BasicBlock *, 4>> inverseSuccessors(
      m_BBToIdx.size());

  for (auto &BB : m_function)
    for (auto *succ : successors(&BB)) {
      m_reach[&BB].set(m_BBToIdx[succ]);
      inverseSuccessors[m_BBToIdx[succ]].insert(&BB);
    }

  bool changed = true;
  while (changed) {
    changed = false;

    // FIXME: Use reverse topo.
    for (auto &BB : llvm::reverse(m_function)) {
      auto &currReach = m_reach[&BB];
      for (BasicBlock *pred : inverseSuccessors[m_BBToIdx[&BB]]) {
        auto &predReach = m_reach[pred];
        const size_t initSize = predReach.count();
        predReach |= currReach;
        if (predReach.count() != initSize)
          changed = true;
      }
    }
  }

  //  for (auto &BB : m_function) {
  //    errs() << BB.getName() << "| " << m_BBToIdx[&BB] << ": ";
  //    for (auto p : llvm::make_range(m_reach[&BB].begin(),
  //    m_reach[&BB].end())) {
  //      errs () << " " << p;
  //    }
  //    errs() << "\n";
  //  }
}

void GateAnalysisImpl::processPhi(PHINode *PN) {
  assert(PN);
  GSA_LOG(PN->print(errs()); errs() << "\n");
  BasicBlock *currentBB = PN->getParent();

  unsigned i = 0;
  for (auto *incomingBB : PN->blocks()) {
    BasicBlock *NCD = getGatingBlock(PN, incomingBB);
    TerminatorInst *terminator = NCD->getTerminator();
    Value *condition = GetCondition(terminator);
    Value *reachingVal = getReachingCmp(currentBB, incomingBB, terminator);

    m_gates[{PN, i}] = Gate{condition, reachingVal};

    GSA_LOG(errs() << "\t" << i << ": " << currentBB->getName() << " <- "
                   << incomingBB->getName() << "\tgate: ";
            condition->print(errs()); errs() << "\n\t\tgating condition: ";
            reachingVal->print(errs()); errs() << "\n");
    ++i;
  }
}

BasicBlock *GateAnalysisImpl::getGatingBlock(PHINode *PN,
                                             BasicBlock *incomingBB) {
  BasicBlock *currentBB = PN->getParent();

  DomTreeNode *DTN = m_DT.getNode(incomingBB);
  while (m_PDT.dominates(incomingBB, DTN->getBlock()) &&
         m_PDT.dominates(currentBB, DTN->getBlock()) &&
         !m_DT.dominates(DTN->getBlock(), currentBB))
    DTN = DTN->getIDom();

  return DTN->getBlock();
}

Value *GateAnalysisImpl::getReachingCmp(BasicBlock *destBB,
                                        BasicBlock *incomingBB,
                                        TerminatorInst *terminator) {
  if (auto *BI = dyn_cast<BranchInst>(terminator)) {
    assert(BI->isConditional());
    BasicBlock *trueSucc = BI->getSuccessor(0);
    BasicBlock *falseSucc = BI->getSuccessor(1);
    assert(trueSucc != falseSucc && "Unconditional branch");

    Value *cond = BI->getCondition();
    StringRef condName = cond->hasName() ? cond->getName() : "";

    // Check which branch always flows to the incoming block.
    if (flowsTo(BI->getParent(), trueSucc, incomingBB, destBB))
      return cond;
    if (flowsTo(BI->getParent(), falseSucc, incomingBB, destBB)) {
      auto it = m_negBranchConditions.find(BI);
      if (it != m_negBranchConditions.end())
        return it->second;

      Value *negCond =
          IRBuilder<>(terminator)
              .CreateICmpEQ(cond,
                            ConstantInt::getFalse(m_function.getContext()),
                            {"seahorn.gsa.br.neg.", condName});
      m_negBranchConditions[BI] = negCond;
      return negCond;
    }

    llvm_unreachable("Neither successor postdominates the incoming block");
  }

  auto *SI = dyn_cast<SwitchInst>(terminator);
  assert(SI && "Must be branch or switch! Other terminators not supported.");

  SmallDenseSet<BasicBlock *, 4> destinations;
  destinations.insert(succ_begin(terminator->getParent()),
                      succ_end(terminator->getParent()));
  for (BasicBlock *succ : destinations) {
    if (flowsTo(SI->getParent(), succ, incomingBB, destBB)) {
      assert(m_switchConditions.count({SI, succ}) > 0);
      return m_switchConditions[{SI, succ}];
    }
  }

  llvm_unreachable("Unhandled case");
}

void GateAnalysisImpl::processSwitch(SwitchInst *SI) {
  assert(SI);

  SmallDenseSet<Value *, 4> caseValues;
  SmallDenseMap<Value *, unsigned> caseValueToIncoming;
  DenseMap<BasicBlock *, SmallDenseSet<Value *, 2>> destValues;
  DenseMap<BasicBlock *, unsigned> destToIdx;

  BasicBlock *defaultDest = SI->getDefaultDest();
  assert(defaultDest && "No default destination");

  Value *caseVal = SI->getCondition();

  for (auto &caseHandle : SI->cases()) {
    assert(caseHandle.getCaseSuccessor() != defaultDest && "Unnecessary case");

    auto *thisVal = caseHandle.getCaseValue();
    unsigned thisIdx = caseHandle.getCaseIndex();
    caseValues.insert(thisVal);
    caseValueToIncoming[thisVal] = thisIdx;
    BasicBlock *dest = caseHandle.getCaseSuccessor();
    destValues[caseHandle.getCaseSuccessor()].insert(thisVal);
    destToIdx[dest] = thisIdx;
  }

  assert(!caseValues.empty() && "Empty switch?");
  assert(!destValues.empty() && "Unconditional switch?");

  // Generate value for default destination.
  SmallVector<Value *, 4> sortedCaseValue(caseValues.begin(), caseValues.end());
  std::sort(sortedCaseValue.begin(), sortedCaseValue.end(),
            [&caseValueToIncoming](Value *first, Value *second) {
              return caseValueToIncoming[first] < caseValueToIncoming[second];
            });

  SmallVector<std::pair<Value *, Value *>, 4> sortedCaseValueToCmp;
  SmallDenseMap<Value *, Value *, 4> caseValueToCmp;
  IRBuilder<> IRB(SI);

  for (Value *V : sortedCaseValue) {
    Value *cmp = IRB.CreateICmpEQ(caseVal, V, "seahorn.gsa.cmp");
    sortedCaseValueToCmp.push_back({V, cmp});
    caseValueToCmp[V] = cmp;
  }

  Value *defaultCond = ConstantInt::getFalse(m_function.getContext());
  for (auto &valueToCmp : sortedCaseValueToCmp)
    defaultCond =
        IRB.CreateOr(defaultCond, valueToCmp.second, "seahorn.gsa.default.or");
  defaultCond = IRB.CreateICmpEQ(defaultCond,
                                 ConstantInt::getFalse(m_function.getContext()),
                                 "seahorn.gsa.default.cond");
  m_switchConditions[{SI, defaultDest}] = defaultCond;

  using DestValuesPair = std::pair<BasicBlock *, SmallDenseSet<Value *, 2>>;
  std::vector<DestValuesPair> sortedDestValues(destValues.begin(),
                                               destValues.end());
  std::sort(
      sortedDestValues.begin(), sortedDestValues.end(),
      [&destToIdx](const DestValuesPair &first, const DestValuesPair &second) {
        return destToIdx[first.first] < destToIdx[second.first];
      });

  for (auto &destToValues : sortedDestValues) {
    assert(!destToValues.second.empty() && "No values for switch destination");
    SmallVector<Value *, 2> values(destToValues.second.begin(),
                                   destToValues.second.end());
    std::sort(values.begin(), values.end(),
              [&caseValueToIncoming](Value *first, Value *second) {
                return caseValueToIncoming[first] < caseValueToIncoming[second];
              });

    Value *cond = caseValueToCmp[values.front()];
    for (size_t i = 1, e = values.size(); i < e; ++i)
      cond =
          IRB.CreateOr(cond, caseValueToCmp[values[i]], "seahorn.gsa.cond.or");

    m_switchConditions[{SI, destToValues.first}] = cond;
  }

  // GSA_LOG(SI->getParent()->print(errs()); errs() << "\n");
}

bool GateAnalysisImpl::flowsTo(BasicBlock *src, BasicBlock *succ,
                               BasicBlock *incoming, BasicBlock *dest) {
  if (succ == dest && incoming == src)
    return true;

  return m_reach[succ].test(m_BBToIdx[incoming]);
}

Gate GateAnalysisImpl::getGatingCondition(PHINode *PN,
                                          size_t incomingArcIndex) const {
  auto it = m_gates.find({PN, static_cast<unsigned short>(incomingArcIndex)});
  assert(it != m_gates.end());
  return it->second;
}

} // anonymous namespace

char GateAnalysisPass::ID = 0;

void GateAnalysisPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<PostDominatorTreeWrapperPass>();
  AU.setPreservesAll();
}

bool GateAnalysisPass::runOnFunction(llvm::Function &F) {
  GSA_LOG(llvm::errs() << "GSA: Running on " << F.getName() << "\n");

  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();

  m_analysis = llvm::make_unique<GateAnalysisImpl>(F, DT, PDT);
  return false;
}

void GateAnalysisPass::print(llvm::raw_ostream &os,
                             const llvm::Module *M) const {
  os << "GateAnalysisPass::print\n";
}

llvm::FunctionPass *createGateAnalysisPass() {
  return new GateAnalysisPass();
}

} // namespace seahorn

static llvm::RegisterPass<seahorn::GateAnalysisPass>
    X("gate-analysis", "Compute Gating functions", true, true);
