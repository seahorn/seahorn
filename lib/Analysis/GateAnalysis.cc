#include "seahorn/Analysis/GateAnalysis.hh"

#include "llvm/Pass.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SparseBitVector.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "avy/AvyDebug.h"

#define GSA_LOG(...) LOG("gsa", __VA_ARGS__)

using namespace llvm;

namespace seahorn {

namespace {

class GateAnalysisImpl : public seahorn::GateAnalysis {
  Function &m_function;
  DominatorTree &m_DT;
  DenseMap<BasicBlock *, unsigned> m_BBToIdx;
  DenseMap<BasicBlock *, SparseBitVector<>> m_reach;

  DenseMap<std::pair<PHINode *, unsigned short>, Gate> m_gates;
  DenseMap<std::pair<SwitchInst *, BasicBlock *>, Value *> m_switchConditions;
  DenseMap<BranchInst *, Value *> m_negBranchConditions;

public:
  GateAnalysisImpl(Function &f, DominatorTree &dt) : m_function(f), m_DT(dt) {
    initReach();
    calculate();
  }

  Gate getGatingCondition(PHINode *PN, size_t incomingArcIndex) const override;

private:
  void calculate();
  void initReach();
  void processSwitch(SwitchInst *SI);
  void processPhi(PHINode *PN);
  Value *getReachingCase(BasicBlock *destBB, BasicBlock *incomingBB,
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
    BasicBlock *NCD = m_DT.findNearestCommonDominator(currentBB, incomingBB);
    TerminatorInst *terminator = NCD->getTerminator();
    Value *condition = GetCondition(terminator);
    Value *reachingVal = getReachingCase(currentBB, incomingBB, terminator);

    m_gates[{PN, i}] = Gate{condition, reachingVal};

    GSA_LOG(errs() << "\t" << i << ": " << currentBB->getName() << " <- "
                   << incomingBB->getName() << "\tgate: ";
            condition->print(errs()); errs() << "\n\t\tgating condition: ";
            reachingVal->print(errs()); errs() << "\n");
    ++i;
  }
}

Value *GateAnalysisImpl::getReachingCase(BasicBlock *destBB,
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
  DenseMap<BasicBlock *, SmallDenseSet<Value *, 2>> destValues;

  BasicBlock *defaultDest = SI->getDefaultDest();
  assert(defaultDest && "No default destination");

  Value *caseVal = SI->getCondition();

  for (auto &caseHandle : SI->cases()) {
    assert(caseHandle.getCaseSuccessor() != defaultDest && "Unnecessary case");

    caseValues.insert(caseHandle.getCaseValue());
    destValues[caseHandle.getCaseSuccessor()].insert(caseHandle.getCaseValue());
  }

  assert(!caseValues.empty() && "Empty switch?");
  assert(!destValues.empty() && "Unconditional switch?");

  IRBuilder<> IRB(SI);
  // Generate value for default destination.
  SmallDenseMap<Value *, Value *, 4> caseValueToCmp;
  for (Value *V : caseValues) {
    Value *cmp = IRB.CreateICmpEQ(caseVal, V, "seahorn.gsa.cmp");
    caseValueToCmp[V] = cmp;
  }

  Value *defaultCond = ConstantInt::getFalse(m_function.getContext());
  for (auto &valueToCmp : caseValueToCmp)
    defaultCond =
        IRB.CreateOr(defaultCond, valueToCmp.second, "seahorn.gsa.default.or");
  defaultCond = IRB.CreateNeg(defaultCond, "seahorn.gsa.default.cond");
  m_switchConditions[{SI, defaultDest}] = defaultCond;

  for (auto &destToValues : destValues) {
    assert(!destToValues.second.empty() && "No values for switch destination");
    SmallVector<Value *, 2> values(destToValues.second.begin(),
                                   destToValues.second.end());
    Value *cond = values.front();
    for (size_t i = 1, e = values.size(); i < e; ++i)
      cond = IRB.CreateOr(cond, values[i], "seahorn.gsa.cond.or");

    m_switchConditions[{SI, destToValues.first}] = cond;
  }

  GSA_LOG(SI->getParent()->print(errs()); errs() << "\n");
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
  AU.setPreservesAll();
}

bool GateAnalysisPass::runOnFunction(llvm::Function &F) {
  GSA_LOG(llvm::errs() << "GSA: Running on " << F.getName() << "\n");

  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();

  m_analysis = llvm::make_unique<GateAnalysisImpl>(F, DT);
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
