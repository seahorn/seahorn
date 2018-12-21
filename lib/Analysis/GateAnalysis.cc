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

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Analysis/ControlDependenceAnalysis.hh"

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
  ControlDependenceAnalysis &m_CDA;

  DenseMap<std::pair<PHINode *, unsigned short>, Gate> m_gates;

public:
  GateAnalysisImpl(Function &f, DominatorTree &dt, PostDominatorTree &pdt,
                   ControlDependenceAnalysis &cda)
      : m_function(f), m_DT(dt), m_PDT(pdt), m_CDA(cda) {
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
  void processPhi(PHINode *PN, IRBuilder<> &IRB);
  DenseMap<BasicBlock *, Value *> processIncomingValues(PHINode *PN,
                                                        IRBuilder<> &IRB);
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
  DenseMap<BasicBlock *, std::unique_ptr<IRBuilder<>>> builders;

  for (auto &BB : m_function) {
    Instruction *insertionPoint = nullptr;
    for (auto &I : BB) {
      if (!isa<PHINode>(I)) {
        insertionPoint = &I;
        break;
      }
    }

    assert(insertionPoint);
    builders.insert({&BB, llvm::make_unique<IRBuilder<>>(insertionPoint)});

    for (auto &I : BB)
      if (auto *PN = dyn_cast<PHINode>(&I))
        phis.push_back(PN);
  }

  for (PHINode *PN : phis)
    processPhi(PN, *builders[PN->getParent()]);
}

struct SuccInfo {
  SmallDenseMap<BasicBlock *, llvm::Optional<Value *>> SuccToIncoming;

  void dump(raw_ostream &OS) const {
    for (auto &SuccValuePair : SuccToIncoming) {
      errs() << "\tsucc: " << SuccValuePair.first->getName() << ": ";
      Value *V = SuccValuePair.second.getValueOr(nullptr);
      if (!V)
        errs() << "T";
      else
        errs() << V->getName();

      errs() << "\n";
    }
  }
};

DenseMap<BasicBlock *, Value *>
GateAnalysisImpl::processIncomingValues(PHINode *PN, IRBuilder<> &IRB) {
  assert(PN);

  BasicBlock *const currentBB = PN->getParent();
  UndefValue *const Undef = UndefValue::get(PN->getType());

  DenseMap<BasicBlock *, Value *> incomingBlockToValue;
  for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
    BasicBlock *incomingBlock = PN->getIncomingBlock(i);
    Value *incomingValue = PN->getIncomingValue(i);
    incomingBlockToValue[incomingBlock] = incomingValue;

    TerminatorInst *TI = incomingBlock->getTerminator();
    assert(isa<BranchInst>(TI) && "Other termiantors not supported yet");
    auto *BI = dyn_cast<BranchInst>(TI);
    if (BI->isUnconditional())
      continue;

    Value *cond = GetCondition(TI);
    BasicBlock *trueDest = BI->getSuccessor(0);
    BasicBlock *falseDest = BI->getSuccessor(1);
    assert(trueDest == currentBB || falseDest == currentBB);
    Value *SI =
        IRB.CreateSelect(cond, trueDest == currentBB ? incomingValue : Undef,
                         falseDest == currentBB ? incomingValue : Undef,
                         {"seahorn.gsa.gamma.crit.", incomingBlock->getName()});
    incomingBlockToValue[incomingBlock] = SI;
  }

  return incomingBlockToValue;
}

void GateAnalysisImpl::processPhi(PHINode *PN, IRBuilder<> &IRB) {
  assert(PN);
  GSA_LOG(PN->print(errs()); errs() << "\n");

  BasicBlock *const currentBB = PN->getParent();

  DenseMap<BasicBlock *, Value *> incomingBlockToValue =
      processIncomingValues(PN, IRB);

  std::vector<CDInfo> cdInfo;
  for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
    auto *BB = PN->getIncomingBlock(i);
    for (const CDInfo &info : m_CDA.getCDBlocks(BB))
      cdInfo.push_back(info);
  }

  std::sort(cdInfo.begin(), cdInfo.end(),
            [this](const CDInfo &first, const CDInfo &second) {
              return m_CDA.getBBTopoIdx(first.CDBlock) >
                     m_CDA.getBBTopoIdx(second.CDBlock);
            });
  cdInfo.erase(std::unique(cdInfo.begin(), cdInfo.end()), cdInfo.end());

  DenseMap<BasicBlock *, Value *> flowingValues(incomingBlockToValue.begin(),
                                                incomingBlockToValue.end());

  Type *const phiTy = PN->getType();
  UndefValue *const Undef = UndefValue::get(phiTy);

  unsigned cdNum = 0;
  for (const CDInfo &info : cdInfo) {
    BasicBlock *BB = info.CDBlock;
    if (flowingValues.count(BB) > 0)
      continue;

    TerminatorInst *TI = BB->getTerminator();
    assert(isa<BranchInst>(TI) && "Only BranchInst is supported right now");

    errs() << "Considering CDInfo " << BB->getName() << "\n";

    SmallDenseMap<BasicBlock *, Value *, 2> SuccToVal;
    for (auto *S : successors(BB)) {
      SuccToVal[S] = Undef;

      for (auto &BlockValuePair : flowingValues) {
        if (m_PDT.dominates(BlockValuePair.first, S)) {
          SuccToVal[S] = BlockValuePair.second;
          errs() << "2) SuccToVal[" << S->getName() << "] = postdom for "
                 << BlockValuePair.first->getName() << ": "
                 << SuccToVal[S]->getName() << "\n";
          break;
        }
      }

      if (SuccToVal[S] != Undef)
        continue;

      for (unsigned i = cdNum - 1; i < cdNum; --i) {
        BasicBlock *OtherCD = cdInfo[i].CDBlock;
        if (m_CDA.isReachable(S, OtherCD)) {
          assert(flowingValues.count(OtherCD));
          SuccToVal[S] = flowingValues[OtherCD];
          errs() << "3) SuccToVal[" << S->getName() << "] = flow for CD "
                 << OtherCD->getName() << ": " << SuccToVal[S]->getName()
                 << "\n";
          break;
        }
      }
    }

    auto *BI = cast<BranchInst>(TI);
    assert(SuccToVal.size() <= 2 && SuccToVal.size() >= 1);
    if (SuccToVal.size() == 1) {
      auto &SuccValPair = *SuccToVal.begin();
      assert(SuccValPair.second != Undef);
      flowingValues[BB] = SuccValPair.second;
    } else if (SuccToVal.size() == 2) {
      BasicBlock *TrueDest = BI->getSuccessor(0);
      BasicBlock *FalseDest = BI->getSuccessor(1);
      Value *TrueVal = SuccToVal[TrueDest];
      Value *FalseVal = SuccToVal[FalseDest];

      const char *namePrefix = (TrueVal != Undef && FalseVal != Undef)
                                   ? "seahorn.gsa.thin_gamma."
                                   : "seahorn.gsa.gamma.";
      Value *Ite = IRB.CreateSelect(BI->getCondition(), TrueVal, FalseVal,
                                    {namePrefix, BB->getName()});
      flowingValues[BB] = Ite;
    }

    ++cdNum;
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
  //  if (auto *BI = dyn_cast<BranchInst>(terminator)) {
  //    assert(BI->isConditional());
  //    BasicBlock *trueSucc = BI->getSuccessor(0);
  //    BasicBlock *falseSucc = BI->getSuccessor(1);
  //    assert(trueSucc != falseSucc && "Unconditional branch");
  //
  //    Value *cond = BI->getCondition();
  //    StringRef condName = cond->hasName() ? cond->getName() : "";
  //
  //    // Check which branch always flows to the incoming block.
  //    if (flowsTo(BI->getParent(), trueSucc, incomingBB, destBB))
  //      return cond;
  //    if (flowsTo(BI->getParent(), falseSucc, incomingBB, destBB)) {
  //      auto it = m_negBranchConditions.find(BI);
  //      if (it != m_negBranchConditions.end())
  //        return it->second;
  //
  //      Value *negCond =
  //          IRBuilder<>(terminator)
  //              .CreateICmpEQ(cond,
  //                            ConstantInt::getFalse(m_function.getContext()),
  //                            {"seahorn.gsa.br.neg.", condName});
  //      m_negBranchConditions[BI] = negCond;
  //      return negCond;
  //    }
  //
  //    llvm_unreachable("Neither successor postdominates the incoming block");
  //  }
  //
  //  auto *SI = dyn_cast<SwitchInst>(terminator);
  //  assert(SI && "Must be branch or switch! Other terminators not
  //  supported.");
  //
  //  SmallDenseSet<BasicBlock *, 4> destinations;
  //  destinations.insert(succ_begin(terminator->getParent()),
  //                      succ_end(terminator->getParent()));
  //  for (BasicBlock *succ : destinations) {
  //    if (flowsTo(SI->getParent(), succ, incomingBB, destBB)) {
  //      assert(m_switchConditions.count({SI, succ}) > 0);
  //      return m_switchConditions[{SI, succ}];
  //    }
  //  }

  return nullptr;
  llvm_unreachable("Unhandled case");
}

bool GateAnalysisImpl::flowsTo(BasicBlock *src, BasicBlock *succ,
                               BasicBlock *incoming, BasicBlock *dest) {
  if (succ == dest && incoming == src)
    return true;

  return m_CDA.isReachable(succ, incoming);
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
  AU.addRequired<ControlDependenceAnalysisPass>();
  AU.setPreservesAll();
}

bool GateAnalysisPass::runOnFunction(llvm::Function &F) {
  GSA_LOG(llvm::errs() << "\nGSA: Running on " << F.getName() << "\n");

  auto &DT = getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>().getPostDomTree();
  auto &CDA = getAnalysis<ControlDependenceAnalysisPass>()
                  .getControlDependenceAnalysis();

  m_analysis = llvm::make_unique<GateAnalysisImpl>(F, DT, PDT, CDA);
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
