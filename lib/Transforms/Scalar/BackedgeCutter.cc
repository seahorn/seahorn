#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Passes.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Transforms/Utils/Local.hh"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/Local.h"

// void FindFunctionBackedges(
//     const Function &F,
//     SmallVectorImpl<std::pair<const BasicBlock *, const BasicBlock *>>
//     &Result);

#define DEBUG_TYPE "back-edge-cutter"
STATISTIC(NumBackEdges, "Number of back-edges");
STATISTIC(NumBackEdgesUncut, "Number of back-edges not cut");

static llvm::cl::opt<bool> AddAssertOnBackEdgeOpt(
    "back-edge-cutter-with-asserts",
    llvm::cl::desc("Add calls to verifier.assert on back-edge to confirm loop "
                   "unrolling is adequate"),
    llvm::cl::init(false));

using namespace llvm;
using namespace seahorn;
namespace {
/// Finds and removes all back-edges in a function
struct BackedgeCutter : public FunctionPass {

  static char ID;

  BackedgeCutter() : FunctionPass(ID) {}
  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<SeaBuiltinsInfoWrapperPass>();
    // preserve nothing
  }

  StringRef getPassName() const override { return "BackedgeCutter"; }
};

char BackedgeCutter::ID = 0;

} // namespace

static void createConditionalAssert(BranchInst &TI, Function &F,
                                    BasicBlock &dst, SeaBuiltinsInfo &SBI) {
  // insert verifier.assert{.not} function
  auto *assertFn =
      SBI.mkSeaBuiltinFn(TI.getSuccessor(0) == &dst ? SeaBuiltinsOp::ASSERT_NOT
                                                    : SeaBuiltinsOp::ASSERT,
                         *F.getParent());
  auto ci = CallInst::Create(assertFn, TI.getCondition(), "", &TI);
  MDNode *meta = MDNode::get(F.getContext(), None);
  ci->setMetadata("backedge_assert", meta);
  // -- a hack to locate a near-by debug location
  if (TI.getDebugLoc())
    ci->setDebugLoc(TI.getDebugLoc());
  else if (auto condInst = dyn_cast<Instruction>(TI.getCondition())) {
    ci->setDebugLoc(condInst->getDebugLoc());
  }
}

static void createUnconditionalAssert(BranchInst &TI, Function &F,
                                      BasicBlock &dst, SeaBuiltinsInfo &SBI) {
  // insert verifier.assert function
  auto *assertFn = SBI.mkSeaBuiltinFn(SeaBuiltinsOp::ASSERT, *F.getParent());
  auto ci = CallInst::Create(assertFn, ConstantInt::getFalse(F.getContext()),
                             "", &TI);
  MDNode *meta = MDNode::get(F.getContext(), None);
  ci->setMetadata("backedge_assert", meta);
  // -- a hack to locate a near-by debug location
  if (TI.getDebugLoc())
    ci->setDebugLoc(TI.getDebugLoc());
}

/// Remove a back-edge
///
/// If the backe-edge is unconditional, replace with assume(false). If the
/// back-edge is conditional, assume condition that forces back-edge to not be
/// taken.
static bool cutBackEdge(BasicBlock *src, BasicBlock *dst, Function &F,
                        SeaBuiltinsInfo &SBI) {
  DOG(INFO << "Cutting back-edge in " << F.getName() << "\n";);
  DOG(llvm::errs() << "Cutting back-edge:\n"
                   << *src << "\n\n to \n\n"
                   << *dst << "\n";);
  auto *TI = dyn_cast<BranchInst>(src->getTerminator());

  if (!TI) {
    DOG(ERR << "not cutting a back-edge. Unhandled terminator: " << *TI);
    ++NumBackEdgesUncut;
    return false;
  }

  if (TI->isUnconditional()) {
    if (AddAssertOnBackEdgeOpt) {
      createUnconditionalAssert(*TI, F, *dst, SBI);
      DOG(INFO << "add unwinding assert for a (un)conditional back edge");
    }
    // -- call assume(false) which will get stuck
    DOG(WARN << "add assume(false) an (un)conditional back edge");
    auto *assumeFn = SBI.mkSeaBuiltinFn(SeaBuiltinsOp::ASSUME, *F.getParent());
    CallInst::Create(assumeFn, ConstantInt::getFalse(F.getContext()), "",
                     const_cast<llvm::BranchInst *>(TI));
    // -- change branch to unreachable because assume(false) above
    llvm::changeToUnreachable(const_cast<llvm::BranchInst *>(TI), false,
                              nullptr, nullptr);
    return true;
  } else {
    assert(TI->getSuccessor(0) == dst || TI->getSuccessor(1) == dst);
    if (AddAssertOnBackEdgeOpt) {
      createConditionalAssert(*TI, F, *dst, SBI);
      DOG(INFO << "add unwinding assert for a conditional back edge");
    }

    auto *assumeFn = SBI.mkSeaBuiltinFn(TI->getSuccessor(0) == dst
                                            ? SeaBuiltinsOp::ASSUME_NOT
                                            : SeaBuiltinsOp::ASSUME,
                                        *F.getParent());
    CallInst::Create(assumeFn, TI->getCondition(), "", TI);

    llvm::for_each(dst->phis(),
                   [&src = src](auto &phi) { phi.removeIncomingValue(src); });

    BranchInst::Create(TI->getSuccessor(0) == dst ? TI->getSuccessor(1)
                                                  : TI->getSuccessor(0),
                       TI);
    TI->eraseFromParent();
    return true;
  }
  llvm_unreachable("Not handled");
}

bool BackedgeCutter::runOnFunction(Function &F) {
  auto &SBI = getAnalysis<SeaBuiltinsInfoWrapperPass>().getSBI();
  llvm::SmallVector<std::pair<const BasicBlock *, const BasicBlock *>, 256>
      BackEdges;
  llvm::FindFunctionBackedges(F, BackEdges);

  bool Changed = false;
  for (auto &edge : BackEdges) {
    ++NumBackEdges;
    Changed |= cutBackEdge(const_cast<BasicBlock *>(edge.first),
                           const_cast<BasicBlock *>(edge.second), F, SBI);
  }

  if (Changed) {
    // -- Clean up after cutting an unconditional back-edge. Such a cut creates
    // -- an unreachable basic block that has to be removed.

    // XXX This only needs to run when an unconditional back-edge was removed,
    // XXX but currently scheduling it if any change has been done at all.
    reduceToReturnPaths(F, SBI);
  }

  return Changed;
}

llvm::Pass *seahorn::createBackEdgeCutterPass() { return new BackedgeCutter(); }
