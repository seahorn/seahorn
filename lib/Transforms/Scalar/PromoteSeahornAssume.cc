#include "llvm/Pass.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"

#include "llvm/IR/IRBuilder.h"

#include "boost/range.hpp"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"

#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/PatternMatch.h"

using namespace llvm;
using namespace llvm::PatternMatch;

namespace {

/// Returns true if v is used by assume
static bool hasAssumeUsers(Value &v) {
  for (User *U : v.users())
    if (CallInst *ci = dyn_cast<CallInst>(U))
      if (match(ci, m_Intrinsic<Intrinsic::assume>()))
        return true;

  return false;
}

class PromoteSeahornAssume : public FunctionPass {
public:
  static char ID;

  PromoteSeahornAssume() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    if (F.empty())
      return false;

    bool Changed = false;

    LLVMContext &ctx = F.getContext();
    IRBuilder<> Builder(ctx);

    for (auto &I : instructions(F)) {
      if (!isa<CallInst>(&I))
        continue;
      // XXX this is a noop, since if this succeeds I is not a CallInst
      Value *v = I.stripPointerCasts();
      assert(isa<CallInst>(v));
      auto &CI = cast<CallInst>(*v);
      const Function *fn = CI.getCalledFunction();
      if (!fn && CI.getCalledOperand())
        fn = dyn_cast<const Function>(CI.getCalledOperand()->stripPointerCasts());

      if (fn && (fn->getName().equals("verifier.assume") ||
                 fn->getName().equals("verifier.assume.not"))) {
        Value *arg = CI.getOperand(0);
        // already used in llvm.assume. skip it.
        if (hasAssumeUsers(*arg))
          continue;

        /* insert after verifier.assume, otherwise, verifier assume
           might get simplified away */
        Builder.SetInsertPoint(I.getParent(), ++BasicBlock::iterator(I));
        /** keep both llvm assume and verifier.assume to make sure
            that LLVM does not touch our assumptions.
            Might revisit this in the future.
        */
        if (fn->getName().equals("verifier.assume.not"))
          arg = Builder.CreateNot(arg);
        CallInst *c = Builder.CreateAssumption(arg);
        /*
           mark this assumption so that we know who inserted it
           use c->getMetadata(seahorn) to test.
        */
        c->setMetadata(F.getParent()->getMDKindID("seahorn"),
                       MDNode::get(ctx, None));
        Changed = true;
      }
    }

    return Changed;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override { AU.setPreservesAll(); }
  virtual StringRef getPassName() const override {
    return "PromoteSeahornAssume";
  }
};

char PromoteSeahornAssume::ID = 0;
}

namespace seahorn {
FunctionPass *createPromoteSeahornAssumePass() {
  return new PromoteSeahornAssume();
}
}

static llvm::RegisterPass<PromoteSeahornAssume>
    X("promote-seahorn-assume",
      "Promote seahorn assume to llvm assume intrinsic");
