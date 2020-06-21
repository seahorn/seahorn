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
#include "seahorn/Support/Stats.hh"

#define GSA_LOG(...) LOG("gsa", __VA_ARGS__)

static llvm::cl::opt<bool> ThinnedGsa("gsa-thinned",
                                      llvm::cl::desc("Emit thin gammas"),
                                      llvm::cl::init(true), llvm::cl::Hidden);

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
  IRBuilder<> m_IRB;

public:
  GateAnalysisImpl(Function &f, DominatorTree &dt, PostDominatorTree &pdt,
                   ControlDependenceAnalysis &cda)
      : m_function(f), m_DT(dt), m_PDT(pdt), m_CDA(cda), m_IRB(f.getContext()) {
    LOG("gsa-dump-before",
        errs()
            << "Dumping IR before running Gated SSA analysis pass on function: "
            << f.getName() << "\n==========================================\n";
        f.print(errs()); errs() << "\n");

    LOG("gsa-view-cfg", f.viewCFG());

    LOG("gsa-view-cfg", m_DT.viewGraph());

    calculate();

    LOG("gsa-dump-after",
        errs()
            << "Dumping IR after running GatedSSA analysis pass on function: "
            << f.getName() << "\n==========================================\n";
        f.print(errs()); errs() << "\n");
  }

  Value *getGamma(PHINode *PN) const override {
    auto it = m_gammas.find(PN);
    assert(it != m_gammas.end());
    return it->second;
  }

  bool isThinned() const override { return ThinnedGsa; }

private:
  void calculate();
  void processPhi(PHINode *PN, Instruction *insertionPt);
  DenseMap<BasicBlock *, Value *>
  processIncomingValues(PHINode *PN, Instruction *insertionPt);
};

Value *GetCondition(Instruction *TI) {
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
  std::vector<PHINode *> phis; // All phis in the function.
  DenseMap<BasicBlock *, Instruction *> insertionPts;

  // Gammas need to be placed just after the last PHI nodes. This is because
  // LLVM utilities expect PHIs to appear at the very beginning of basic blocks.
  // We want to append gamma nodes (SelectInsts) after one another, as they can
  // depend on previously executed gammas.
  for (auto &BB : m_function) {
    Instruction *insertionPoint = BB.getFirstNonPHI();
    assert(insertionPoint);
    insertionPts.insert({&BB, insertionPoint});

    for (auto &PN : BB.phis())
      phis.push_back(&PN);
  }

  for (PHINode *PN : phis) {
    auto *BB = PN->getParent();
    processPhi(PN, insertionPts[BB]);
  }
}

// Construct gating functions for incoming critical edges in the GSA mode.
// Construct a mapping between incoming blocks to values.
DenseMap<BasicBlock *, Value *>
GateAnalysisImpl::processIncomingValues(PHINode *PN, Instruction *insertionPt) {
  assert(PN);

  BasicBlock *const currentBB = PN->getParent();
  m_IRB.SetInsertPoint(insertionPt);
  UndefValue *const Undef = UndefValue::get(PN->getType());

  DenseMap<BasicBlock *, Value *> incomingBlockToValue;
  for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
    BasicBlock *incomingBlock = PN->getIncomingBlock(i);
    Value *incomingValue = PN->getIncomingValue(i);
    incomingBlockToValue[incomingBlock] = incomingValue;

    auto *TI = incomingBlock->getTerminator();
    assert(isa<BranchInst>(TI) && "Other termiantors not supported yet");
    auto *BI = dyn_cast<BranchInst>(TI);
    if (BI->isUnconditional())
      continue;

    Value *cond = GetCondition(TI);
    BasicBlock *trueDest = BI->getSuccessor(0);
    BasicBlock *falseDest = BI->getSuccessor(1);
    assert(trueDest == currentBB || falseDest == currentBB);

    if (!ThinnedGsa) {
      Value *SI = m_IRB.CreateSelect(
          cond, trueDest == currentBB ? incomingValue : Undef,
          falseDest == currentBB ? incomingValue : Undef,
          {"seahorn.gsa.gamma.crit.", incomingBlock->getName()});
      incomingBlockToValue[incomingBlock] = SI;
    }
  }

  return incomingBlockToValue;
}

void GateAnalysisImpl::processPhi(PHINode *PN, Instruction *insertionPt) {
  assert(PN);
  GSA_LOG(PN->print(errs()); errs() << "\n");

  BasicBlock *const currentBB = PN->getParent();
  DenseMap<BasicBlock *, Value *> incomingBlockToValue =
      processIncomingValues(PN, insertionPt);

  // Make sure CD blocks are sorted in reverse-topological order. We need this
  // because we want to process them in order opposite to execution order.
  auto GreaterThanTopo = [this](BasicBlock *first, BasicBlock *second) {
    return m_CDA.getBBTopoIdx(first) > m_CDA.getBBTopoIdx(second);
  };
  // TODO: Look into the performance effects of using a set wrt a vector.
  // For now we use a set since, the number of redundant blocks are huge. Using
  // a set results in a smaller time complexity.
  std::set<BasicBlock *, decltype(GreaterThanTopo)> cdInfo(GreaterThanTopo);
  // Collect all blocks the incoming blocks are control dependent on.
  for (unsigned i = 0, e = PN->getNumIncomingValues(); i != e; ++i) {
    auto *BB = PN->getIncomingBlock(i);
    for (BasicBlock *CDBlock : m_CDA.getCDBlocks(BB))
      cdInfo.insert(CDBlock);
  }

  // Mapping from blocks in cdInfo to values potentially guarded by gammas.
  DenseMap<BasicBlock *, Value *> flowingValues(incomingBlockToValue.begin(),
                                                incomingBlockToValue.end());

  Type *const phiTy = PN->getType();
  UndefValue *const Undef = UndefValue::get(phiTy);
  m_IRB.SetInsertPoint(insertionPt);

  // For all blocks in cdInfo and inspect their successors to construct gamma
  // nodes where needed.
  GSA_LOG(errs() << "CDInfo size: " << cdInfo.size() << "\n");
  for (BasicBlock *BB : cdInfo) {
    GSA_LOG(errs() << "CDBlock: " << BB->getName() << "\n");

    auto *TI = BB->getTerminator();
    assert(isa<BranchInst>(TI) && "Only BranchInst is supported right now");

    GSA_LOG(errs() << "Considering CDInfo " << BB->getName() << "\n");

    // Collect all successors and associated values that flows when they are
    // taken (or Undef if no such flow exists).
    SmallDenseMap<BasicBlock *, Value *, 2> SuccToVal;
    for (auto *S : successors(BB)) {
      GSA_LOG(errs() << "\tsuccessor " << S->getName() << "\n");
      // Either no values flows.
      SuccToVal[S] = Undef;

      // Or this is a direct branch to the PHI's parent block.
      if (S == currentBB) {
        SuccToVal[S] = incomingBlockToValue[BB];
        GSA_LOG({
          errs() << "1) SuccToVal[" << S->getName() << "] = direct branch to "
                 << currentBB->getName() << ": " << SuccToVal[S]->getName()
                 << "\n";
        });
      }

      if (SuccToVal[S] != Undef)
        continue;

      // Or the successors unconditionally flows to an already processed block.
      // Note that there can be at most one such block.

      // Used to iterate over all the post-dominators of `S`.
      BasicBlock *postDomBlock = S;
      while (postDomBlock) {
        auto it = flowingValues.find(postDomBlock);
        if (it != flowingValues.end()) {
          SuccToVal[S] = it->second;
          GSA_LOG(errs() << "2) SuccToVal[" << S->getName()
                         << "] = postdom for cd " << postDomBlock->getName()
                         << ": " << it->second->getName() << "\n");
          break;
        }
        auto *treeNode = m_PDT.getNode(postDomBlock)->getIDom();
        if (treeNode == nullptr) {
          break;
        }
        postDomBlock = treeNode->getBlock();
      }
    }

    auto *BI = cast<BranchInst>(TI);
    assert(1 <= SuccToVal.size() && SuccToVal.size() <= 2);
    if (SuccToVal.size() == 1) {
      auto &SuccValPair = *SuccToVal.begin();
      assert(SuccValPair.second != Undef);
      flowingValues[BB] = SuccValPair.second;
    } else if (SuccToVal.size() == 2) {
      BasicBlock *TrueDest = BI->getSuccessor(0);
      BasicBlock *FalseDest = BI->getSuccessor(1);
      Value *TrueVal = SuccToVal[TrueDest];
      Value *FalseVal = SuccToVal[FalseDest];

      // Construct gamma node only when necessary.
      assert(TrueVal != Undef || FalseVal != Undef);
      if (TrueVal == FalseVal) {
        flowingValues[BB] = TrueVal;
      } else if (ThinnedGsa && (TrueVal == Undef || FalseVal == Undef)) {
        flowingValues[BB] = FalseVal == Undef ? TrueVal : FalseVal;
      } else {
        // Gammas as expressed as SelectInsts and placed in the analyzed IR.
        Value *Ite = m_IRB.CreateSelect(BI->getCondition(), TrueVal, FalseVal,
                                        {"seahorn.gsa.gamma.", BB->getName()});
        flowingValues[BB] = Ite;
      }
    }
  }

  BasicBlock *IDomBlock = m_DT.getNode(currentBB)->getIDom()->getBlock();
  assert(IDomBlock);
  assert(flowingValues.count(IDomBlock));

  Value *gamma = flowingValues[IDomBlock];
  Twine newName = gamma->getName() + ".y." + PN->getName();
  gamma->setName(newName);
  m_gammas[PN] = gamma;

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
  AU.addRequired<DominatorTreeWrapperPass>();
  AU.addRequired<PostDominatorTreeWrapperPass>();
  AU.setPreservesAll();
}

bool GateAnalysisPass::runOnModule(llvm::Module &M) {
  Stats::resume("Thinned Gate SSA transformation");
  auto &CDP = getAnalysis<ControlDependenceAnalysisPass>();

  bool changed = false;
  for (auto &F : M)
    if (!F.isDeclaration())
      changed |= runOnFunction(F, CDP.getControlDependenceAnalysis(F));

  Stats::stop("Thinned Gate SSA transformation");

  LOG("gsa", if (GsaReplacePhis) for (
                 auto &F
                 : M) if (!F.isDeclaration()) for (auto &BB
                                                   : F) for (auto &I
                                                             : BB)
                 assert(!isa<PHINode>(I)));

  return changed;
}

bool GateAnalysisPass::runOnFunction(llvm::Function &F,
                                     ControlDependenceAnalysis &CDA) {
  GSA_LOG(llvm::errs() << "\nGSA: Running on " << F.getName() << "\n");

  auto &DT = getAnalysis<DominatorTreeWrapperPass>(F).getDomTree();
  auto &PDT = getAnalysis<PostDominatorTreeWrapperPass>(F).getPostDomTree();

  m_analyses[&F] = std::make_unique<GateAnalysisImpl>(F, DT, PDT, CDA);
  return false;
}

void GateAnalysisPass::print(llvm::raw_ostream &os,
                             const llvm::Module *) const {
  os << "GateAnalysisPass::print\n";
}

llvm::ModulePass *createGateAnalysisPass() { return new GateAnalysisPass(); }

} // namespace seahorn

static llvm::RegisterPass<seahorn::GateAnalysisPass>
    X("gate-analysis", "Compute Gating functions", true, true);
