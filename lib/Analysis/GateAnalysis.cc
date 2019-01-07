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

#include "seahorn/Support/SeaDebug.h"

#define GSA_LOG(...) LOG("gsa", __VA_ARGS__)

static llvm::cl::opt<bool>
    GsaDumpAfter("gsa-dump-after",
                 llvm::cl::desc("Dump function after running"),
                 llvm::cl::init(false));

static llvm::cl::opt<bool>
    GsaDumpBefore("gsa-dump-before",
                  llvm::cl::desc("Dump function before running"),
                  llvm::cl::init(false));

static llvm::cl::opt<bool>
    GsaViewDomTree("gsa-view-domtree",
                  llvm::cl::desc("View Dominator Tree before GSA"),
                  llvm::cl::init(false));

static llvm::cl::opt<bool> ThinnedGsa("gsa-thinned",
                                      llvm::cl::desc("Emit thin gammas"),
                                      llvm::cl::init(true));

static llvm::cl::opt<bool>
    GsaReplacePhis("gsa-replace-phis",
                   llvm::cl::desc("Replace phis with gammas"),
                   llvm::cl::init(true));

using namespace llvm;

namespace seahorn {

namespace {

class GateAnalysisImpl : public seahorn::GateAnalysis {
  Function &m_function;
  DominatorTree &m_DT;
  PostDominatorTree &m_PDT;
  ControlDependenceAnalysis &m_CDA;

  DenseMap<PHINode *, Value *> m_gammas;

public:
  GateAnalysisImpl(Function &f, DominatorTree &dt, PostDominatorTree &pdt,
                   ControlDependenceAnalysis &cda)
      : m_function(f), m_DT(dt), m_PDT(pdt), m_CDA(cda) {
    if (GsaDumpBefore) {
      errs()
          << "Dumping IR before running Gated SSA analysis pass on function: "
          << f.getName() << "\n==========================================\n";
      f.print(errs());
      errs() << "\n";
      f.viewCFG();
    }

    if (GsaViewDomTree)
      m_DT.viewGraph();

    calculate();

    if (GsaDumpAfter) {
      errs() << "Dumping IR after running GatedSSA analysis pass on function: "
             << f.getName() << "\n==========================================\n";
      f.print(errs());
      errs() << "\n";
    }
  }

  Value *getGamma(PHINode *PN) const override {
    auto it = m_gammas.find(PN);
    assert(it != m_gammas.end());
    return it->second;
  }

  bool isThinned() const override { return false; }

private:
  void calculate();
  void processPhi(PHINode *PN, IRBuilder<> &IRB);
  DenseMap<BasicBlock *, Value *> processIncomingValues(PHINode *PN,
                                                        IRBuilder<> &IRB);
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

    if (ThinnedGsa) {
      incomingBlockToValue[incomingBlock] = incomingValue;
    } else {
      Value *SI = IRB.CreateSelect(
          cond, trueDest == currentBB ? incomingValue : Undef,
          falseDest == currentBB ? incomingValue : Undef,
          {"seahorn.gsa.gamma.crit.", incomingBlock->getName()});
      incomingBlockToValue[incomingBlock] = SI;
    }
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
  GSA_LOG(errs() << "CDInfo size: " << cdInfo.size() << "\n");
  for (const CDInfo &info : cdInfo) {
    BasicBlock *BB = info.CDBlock;
    GSA_LOG(errs() << "CDBlock: " << BB->getName() << "\n");
    //    if (flowingValues.count(BB) > 0)
    //      continue;

    TerminatorInst *TI = BB->getTerminator();
    assert(isa<BranchInst>(TI) && "Only BranchInst is supported right now");

    GSA_LOG(errs() << "Considering CDInfo " << BB->getName() << "\n");

    SmallDenseMap<BasicBlock *, Value *, 2> SuccToVal;
    for (auto *S : successors(BB)) {
      GSA_LOG(errs() << "\tsuccessor " << S->getName() << "\n");
      SuccToVal[S] = Undef;

      if (S == currentBB) {
        SuccToVal[S] = incomingBlockToValue[BB];
        GSA_LOG(errs() << "1) SuccToVal[" << S->getName()
                       << "] = direct branch to " << currentBB->getName()
                       << ": " << SuccToVal[S]->getName() << "\n");
      }

      if (SuccToVal[S] != Undef)
        continue;

      for (auto &BlockValuePair : flowingValues) {
        if (m_PDT.dominates(BlockValuePair.first, S)) {
          SuccToVal[S] = BlockValuePair.second;
          GSA_LOG(errs() << "2) SuccToVal[" << S->getName()
                         << "] = postdom for cd "
                         << BlockValuePair.first->getName() << ": "
                         << SuccToVal[S]->getName() << "\n");
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
          GSA_LOG(errs() << "3) SuccToVal[" << S->getName()
                         << "] = flow for CD " << OtherCD->getName() << ": "
                         << SuccToVal[S]->getName() << "\n");
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

      assert(TrueVal != Undef || FalseVal != Undef);
      if (TrueVal == FalseVal) {
        flowingValues[BB] = TrueVal;
      } else if (ThinnedGsa && (TrueVal == Undef || FalseVal == Undef)) {
        flowingValues[BB] = FalseVal == Undef ? TrueVal : FalseVal;
      } else {
        Value *Ite = IRB.CreateSelect(BI->getCondition(), TrueVal, FalseVal,
                                      {"seahorn.gsa.gamma.", BB->getName()});
        flowingValues[BB] = Ite;
      }
    }

    ++cdNum;
  }

  BasicBlock *IDomBlock = m_DT.getNode(currentBB)->getIDom()->getBlock();
  assert(IDomBlock);
  assert(flowingValues.count(IDomBlock));

  Value *gamma = flowingValues[IDomBlock];
  std::string newName = gamma->getName().str() + ".y." + PN->getName().str();
  gamma->setName(newName);
  m_gammas[PN] = flowingValues[IDomBlock];

  GSA_LOG(errs() << "Gamma for phi: " << PN->getName() << "\n\t");
  GSA_LOG(m_gammas[PN]->print(errs()));
  GSA_LOG(errs() << "\n");
  if (GsaReplacePhis) {
    PN->replaceAllUsesWith(gamma);
    PN->eraseFromParent();
  }
}

} // anonymous namespace

char GateAnalysisPass::ID = 0;

void GateAnalysisPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.addRequired<ControlDependenceAnalysisPass>();
  AU.setPreservesAll();
}

bool GateAnalysisPass::runOnModule(llvm::Module &M) {
  auto &CDP = getAnalysis<ControlDependenceAnalysisPass>();

  bool changed = false;
  for (auto &F : M)
    if (!F.isDeclaration())
      changed |= runOnFunction(F, CDP.getControlDependenceAnalysis(F));

  if (GsaReplacePhis)
    for (auto &F : M)
      if (!F.isDeclaration())
        for (auto &BB : F)
          for (auto &I : BB)
            assert(!isa<PHINode>(I));

  return changed;
}

bool GateAnalysisPass::runOnFunction(llvm::Function &F,
                                     ControlDependenceAnalysis &CDA) {
  GSA_LOG(llvm::errs() << "\nGSA: Running on " << F.getName() << "\n");

  //  auto &DT = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
  //  auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();
  DominatorTree DT(F);
  PostDominatorTree PDT;
  PDT.recalculate(F);

  m_analyses[&F] = llvm::make_unique<GateAnalysisImpl>(F, DT, PDT, CDA);
  return false;
}

void GateAnalysisPass::print(llvm::raw_ostream &os,
                             const llvm::Module *M) const {
  os << "GateAnalysisPass::print\n";
}

llvm::ModulePass *createGateAnalysisPass() { return new GateAnalysisPass(); }

} // namespace seahorn

static llvm::RegisterPass<seahorn::GateAnalysisPass>
    X("gate-analysis", "Compute Gating functions", true, true);
