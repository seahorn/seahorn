#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Passes.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/Local.h"

// void FindFunctionBackedges(
//     const Function &F,
//     SmallVectorImpl<std::pair<const BasicBlock *, const BasicBlock *>>
//     &Result);

#define DEBUG_TYPE "back-edge-cutter"
STATISTIC(NumBackEdges, "Number of back-edges");
STATISTIC(NumBackEdgesUncut, "Number of back-edges not cut");

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

/// Remove a back-edge
///
/// If the backe-edge is unconditional, replace with assume(false). If the
/// back-edge is conditional, assume condition that forces back-edge to not be
/// taken.
static bool cutBackEdge(BasicBlock *src, BasicBlock *dst, Function &F,
                        SeaBuiltinsInfo &SBI) {
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
    // -- call assume(false) which will get stuck
    auto *assumeFn = SBI.mkSeaBuiltinFn(SeaBuiltinsOp::ASSUME, *F.getParent());
    CallInst::Create(assumeFn, ConstantInt::getFalse(F.getContext()), "",
                     const_cast<llvm::BranchInst *>(TI));
    // -- change branch to unreachable because assume(false) above
    llvm::changeToUnreachable(const_cast<llvm::BranchInst *>(TI), false, false,
                              nullptr, nullptr);
    return true;
  } else {
    assert(TI->getSuccessor(0) == dst || TI->getSuccessor(1) == dst);
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
  return Changed;
}

llvm::Pass *seahorn::createBackEdgeCutterPass() { return new BackedgeCutter(); }
