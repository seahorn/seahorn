/// Lower LLVM 16's llvm.threadlocal.address intrinsic.
///
/// LLVM 16 added @llvm.threadlocal.address, which clang-16 emits for every
/// access to a thread_local global (e.g. aws-c-common's tl_last_error). The
/// intrinsic returns the calling thread's instance of the global. SeaHorn's
/// operational semantics is single-threaded, so that instance is simply the
/// underlying global -- replace each call with its operand. Without this the
/// opsem treats the intrinsic as an unhandled call (nondet), which makes
/// thread-local reads (error codes) arbitrary and breaks otherwise-valid proofs.
#include "seahorn/SeaNewPmPasses.hh"

#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Intrinsics.h"

using namespace llvm;

namespace {
bool lowerThreadLocalAddress(Function &F) {
  SmallVector<CallInst *, 8> toErase;
  for (auto &I : instructions(F)) {
    auto *CI = dyn_cast<CallInst>(&I);
    if (!CI)
      continue;
    Function *callee = CI->getCalledFunction();
    if (callee && callee->getIntrinsicID() == Intrinsic::threadlocal_address) {
      CI->replaceAllUsesWith(CI->getArgOperand(0));
      toErase.push_back(CI);
    }
  }
  for (auto *CI : toErase)
    CI->eraseFromParent();
  return !toErase.empty();
}
} // namespace

llvm::PreservedAnalyses
seahorn::LowerThreadLocalAddressPass::run(llvm::Function &F,
                                          llvm::FunctionAnalysisManager &) {
  return lowerThreadLocalAddress(F) ? llvm::PreservedAnalyses::none()
                                    : llvm::PreservedAnalyses::all();
}
