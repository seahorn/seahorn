/**
 Lowers calls to sea.is_dereferenceable() that can be resolved statically
*/

#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Passes.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/Module.h"

using namespace llvm;
using namespace seahorn;

#define DEBUG_TYPE "lower-deref"
namespace seahorn {
Value *lowerIsDereferenceable(CallBase *IsDerefCall, const DataLayout &DL,
                              const TargetLibraryInfo *TLI);
}

STATISTIC(NumIsDerefLower, "Number of sea.is_dereferenceable lowered");

namespace {

struct LowerIsDeref : public FunctionPass {
  static char ID;

  LowerIsDeref() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;
  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<SeaBuiltinsInfoWrapperPass>();
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.setPreservesAll();
  }
  StringRef getPassName() const override { return "LowerIsDeref"; }
};
char LowerIsDeref::ID = 0;
} // namespace

bool LowerIsDeref::runOnFunction(Function &F) {
  auto &SBI = getAnalysis<SeaBuiltinsInfoWrapperPass>().getSBI();
  auto &TLI = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
  auto &DL = F.getParent()->getDataLayout();

  bool Changed = false;

  SmallVector<CallInst *, 32> deadCalls;
  for (auto &BB : F) {
    for (auto &I : BB) {
      if (auto *CB = dyn_cast<CallInst>(&I)) {
        if (SBI.getSeaBuiltinOp(*CB) != SeaBuiltinsOp::IS_DEREFERENCEABLE)
          continue;

        // this is a call to sea.is_dereferenceable
        Value *res = lowerIsDereferenceable(CB, DL, &TLI);
        if (res) {
          NumIsDerefLower++;
          CB->replaceAllUsesWith(res);
          deadCalls.push_back(CB);
          Changed = true;
        }
      }
    }
    for (auto &DC : deadCalls) {
      DC->eraseFromParent();
    }
    deadCalls.clear();
  }
  return Changed;
}

/**
   Lowers calls to sea.is_dereferenceable() to true/false if possible

   Statically computes size of a pointer being checked and compares
   the size.
 */
Value *seahorn::lowerIsDereferenceable(CallBase *IsDerefCall,
                                       const DataLayout &DL,
                                       const TargetLibraryInfo *TLI) {

  ObjectSizeOpts EvalOptions;
  EvalOptions.EvalMode = ObjectSizeOpts::Mode::Exact;
  EvalOptions.NullIsUnknownSize = false;
  auto *ResultType = IsDerefCall->getType();

  if (auto *CI = dyn_cast<ConstantInt>(IsDerefCall->getArgOperand(1))) {
    int64_t Requested = CI->getSExtValue();
    // for now, bail out on negative offsets
    // llvm::getObjectSize() bails out on them as well
    if (Requested < 0)
      return nullptr;

    uint64_t Size;
    if (llvm::getObjectSize(IsDerefCall->getArgOperand(0), Size, DL, TLI,
                            EvalOptions)) {
      auto &C = IsDerefCall->getContext();
      return Requested <= Size ? ConstantInt::getTrue(C)
                               : ConstantInt::getFalse(C);
    }
  }

  return nullptr;
}

llvm::Pass *seahorn::createLowerIsDerefPass() { return new LowerIsDeref(); }
