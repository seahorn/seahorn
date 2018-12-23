#include "seahorn/Analysis/ControlDependenceAnalysis.hh"

#include "llvm/Pass.h"

#include "llvm/IR/CFG.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"

#include "llvm/Analysis/IteratedDominanceFrontier.h"
#include "llvm/Analysis/PostDominators.h"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SparseBitVector.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "avy/AvyDebug.h"

#define CDA_LOG(...) LOG("cda", __VA_ARGS__)

static llvm::cl::opt<bool> CDADumpAfter(
    "cda-dump-after",
    llvm::cl::desc("Dump function after running Control Dependence Analysis"),
    llvm::cl::init(false));

using namespace llvm;

namespace seahorn {

namespace {

class ControlDependenceAnalysisImpl
    : public seahorn::ControlDependenceAnalysis {
  Function &m_function;
  DominatorTree &m_DT;
  PostDominatorTree &m_PDT;

  DenseMap<BasicBlock *, unsigned> m_BBToIdx;
  mutable DenseMap<BasicBlock *, SparseBitVector<>> m_reach;
  DenseMap<std::pair<SwitchInst *, BasicBlock *>, Value *> m_switchConditions;
  DenseMap<BranchInst *, Value *> m_negBranchConditions;
  DenseMap<BasicBlock *, SmallVector<CDInfo, 4>> m_cdInfo;

public:
  ControlDependenceAnalysisImpl(Function &f, DominatorTree &dt,
                                PostDominatorTree &pdt)
      : m_function(f), m_DT(dt), m_PDT(pdt) {
    initReach();
    calculate();

    if (CDADumpAfter) {
      errs() << "Dumping IR after running Control Dependence analysis pass on "
                "function: "
             << f.getName() << "\n==========================================\n";
      f.print(errs());
      errs() << "\n";
    }
  }

  ArrayRef<CDInfo> getCDBlocks(BasicBlock *BB) const override;
  bool isReachable(BasicBlock *Src, BasicBlock *Dst) const override;
  virtual unsigned getBBTopoIdx(llvm::BasicBlock *BB) const override {
    auto it = m_BBToIdx.find(BB);
    assert(it != m_BBToIdx.end());
    return it->second;
  }

private:
  void calculate();
  void initReach();
  void processSwitch(SwitchInst *SI);
  void processBranch(BranchInst *BI);
  Value *getReachingCmp(BasicBlock *destBB, TerminatorInst *terminator);
  bool flowsTo(BasicBlock *src, BasicBlock *succ, BasicBlock *dest);
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

void ControlDependenceAnalysisImpl::calculate() {
  std::vector<PHINode *> phis;

  for (auto &BB : m_function) {
    for (auto &I : BB) {
      if (auto *PN = dyn_cast<PHINode>(&I)) {
        phis.push_back(PN);
      }
    }

    if (auto *SI = dyn_cast<SwitchInst>(BB.getTerminator()))
      processSwitch(SI);

    if (auto *BI = dyn_cast<BranchInst>(BB.getTerminator()))
      if (BI->isConditional())
        processBranch(BI);
  }

  for (BasicBlock &BB : m_function) {
    errs() << BB.getName() << ":\n";
    ReverseIDFCalculator calculator(m_PDT);
    SmallPtrSet<BasicBlock *, 1> incoming = {&BB};

    calculator.setDefiningBlocks(incoming);
    SmallVector<BasicBlock *, 4> RDF;
    calculator.calculate(RDF);

    for (auto *CD : RDF) {
      CDA_LOG(errs() << "\t" << CD->getName());
      TerminatorInst *terminator = CD->getTerminator();
      Value *condition = GetCondition(terminator);
      Value *reachingVal = getReachingCmp(&BB, terminator);
      CDA_LOG(errs() << "\tterminator cond: " << condition->getName()
                     << "\tvalue: " << reachingVal->getName() << "\n");
      m_cdInfo[&BB].push_back({CD, reachingVal});
    }
    errs() << "\n";
  }

  errs() << "\n";

  BasicBlock *entry = &m_function.getEntryBlock();

  std::vector<BasicBlock *> poBlocks;
  DenseMap<BasicBlock *, unsigned> topoNums;
  unsigned num = 0;
  for (BasicBlock *BB : llvm::post_order(entry)) {
    poBlocks.push_back(BB);
    topoNums[BB] = num;
    ++num;
  }

  for (auto &BBToVec : m_cdInfo) {
    SmallVectorImpl<CDInfo> &vec = BBToVec.second;
    std::sort(vec.begin(), vec.end(),
              [&topoNums](const CDInfo &first, const CDInfo &second) {
                return topoNums[first.CDBlock] < topoNums[second.CDBlock];
              });
  }

  CDA_LOG(for (BasicBlock *BB
               : llvm::reverse(poBlocks)) {
    errs() << "cd(" << BB->getName() << "): ";
    for (const CDInfo &cdi : m_cdInfo[BB])
      errs() << cdi.CDBlock->getName() << ", ";
    errs() << "\n";
  });
}

void ControlDependenceAnalysisImpl::initReach() {
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
}

Value *
ControlDependenceAnalysisImpl::getReachingCmp(BasicBlock *destBB,
                                              TerminatorInst *terminator) {
  if (auto *BI = dyn_cast<BranchInst>(terminator)) {
    assert(BI->isConditional());
    BasicBlock *trueSucc = BI->getSuccessor(0);
    BasicBlock *falseSucc = BI->getSuccessor(1);
    assert(trueSucc != falseSucc && "Unconditional branch");

    Value *cond = BI->getCondition();

    // Check which branch always flows to the incoming block.
    if (flowsTo(BI->getParent(), trueSucc, destBB))
      return cond;
    if (flowsTo(BI->getParent(), falseSucc, destBB)) {
      assert(m_negBranchConditions.count(BI) > 0);
      return m_negBranchConditions[BI];
    }

    llvm_unreachable("Neither successor postdominates the incoming block");
  }

  auto *SI = dyn_cast<SwitchInst>(terminator);
  assert(SI && "Must be branch or switch! Other terminators not supported.");

  SmallDenseSet<BasicBlock *, 4> destinations;
  destinations.insert(succ_begin(terminator->getParent()),
                      succ_end(terminator->getParent()));
  for (BasicBlock *succ : destinations) {
    if (flowsTo(SI->getParent(), succ, destBB)) {
      assert(m_switchConditions.count({SI, succ}) > 0);
      return m_switchConditions[{SI, succ}];
    }
  }

  llvm_unreachable("Unhandled case");
}

void ControlDependenceAnalysisImpl::processSwitch(SwitchInst *SI) {
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
    Value *cmp = IRB.CreateICmpEQ(caseVal, V, "seahorn.cda.cmp");
    sortedCaseValueToCmp.push_back({V, cmp});
    caseValueToCmp[V] = cmp;
  }

  Value *defaultCond = ConstantInt::getFalse(m_function.getContext());
  for (auto &valueToCmp : sortedCaseValueToCmp)
    defaultCond =
        IRB.CreateOr(defaultCond, valueToCmp.second, "seahorn.cda.default.or");
  defaultCond = IRB.CreateICmpEQ(defaultCond,
                                 ConstantInt::getFalse(m_function.getContext()),
                                 "seahorn.cda.default.cond");
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
          IRB.CreateOr(cond, caseValueToCmp[values[i]], "seahorn.cda.cond.or");

    m_switchConditions[{SI, destToValues.first}] = cond;
  }
}

void ControlDependenceAnalysisImpl::processBranch(BranchInst *BI) {
  assert(BI);
  assert(BI->isConditional());
  BasicBlock *trueSucc = BI->getSuccessor(0);
  BasicBlock *falseSucc = BI->getSuccessor(1);
  assert(trueSucc != falseSucc && "Unconditional branch");

  Value *cond = BI->getCondition();
  StringRef condName = cond->hasName() ? cond->getName() : "";

  Value *negCond = IRBuilder<>(BI).CreateICmpEQ(
      cond, ConstantInt::getFalse(m_function.getContext()),
      {"seahorn.cda.br.neg.", condName});
  m_negBranchConditions[BI] = negCond;
}

bool ControlDependenceAnalysisImpl::flowsTo(BasicBlock *src, BasicBlock *succ,
                                            BasicBlock *dest) {
  assert((llvm::find(llvm::successors(src), succ) != llvm::succ_end(src)) &&
         "Not a successor");
  (void)src;
  if (succ == dest)
    return true;

  return m_reach[succ].test(m_BBToIdx[dest]);
}

llvm::ArrayRef<CDInfo>
ControlDependenceAnalysisImpl::getCDBlocks(llvm::BasicBlock *BB) const {
  auto it = m_cdInfo.find(BB);
  assert(it != m_cdInfo.end());
  return it->second;
}

bool ControlDependenceAnalysisImpl::isReachable(BasicBlock *Src,
                                                BasicBlock *Dst) const {
  auto it = m_reach.find(Src);
  assert(it != m_reach.end());
  auto dstIdxIt = m_BBToIdx.find(Dst);
  assert(dstIdxIt != m_BBToIdx.end());
  return it->second.test(dstIdxIt->second);
}

} // anonymous namespace

char ControlDependenceAnalysisPass::ID = 0;

void ControlDependenceAnalysisPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool ControlDependenceAnalysisPass::runOnModule(llvm::Module &M) {
  bool changed = false;
  for (auto &F : M)
    if (!F.isDeclaration())
      changed |= runOnFunction(F);
  return changed;
}

bool ControlDependenceAnalysisPass::runOnFunction(llvm::Function &F) {
  CDA_LOG(llvm::errs() << "CDA: Running on " << F.getName() << "\n");

  // auto &DT = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
  // auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();
  DominatorTree DT(F);
  PostDominatorTree PDT;
  PDT.recalculate(F);

  m_analysis = llvm::make_unique<ControlDependenceAnalysisImpl>(F, DT, PDT);
  return false;
}

void ControlDependenceAnalysisPass::print(llvm::raw_ostream &os,
                                          const llvm::Module *) const {
  os << "ControlDependenceAnalysisPass::print\n";
}

llvm::ModulePass *createControlDependenceAnalysisPass() {
  return new ControlDependenceAnalysisPass();
}

} // namespace seahorn

static llvm::RegisterPass<seahorn::ControlDependenceAnalysisPass>
    X("cd-analysis", "Compute Control Dependence", true, true);
