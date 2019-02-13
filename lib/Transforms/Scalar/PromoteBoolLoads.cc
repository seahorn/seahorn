#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Pass.h"

#include "boost/range.hpp"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;
namespace {
class PromoteBoolLoads : public FunctionPass {
public:
  static char ID;
  PromoteBoolLoads() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) {
    if (F.isDeclaration())
      return false;
    IRBuilder<> B(F.getContext());

    bool changed = false;

    for (auto &bb : F) {
      auto I = bb.begin();
      auto E = bb.end();
      while (I != E) {
        if (TruncInst *trunc = dyn_cast<TruncInst>(&*I)) {
          // op = load i8 ... ; x = truc i8 op to i1
          if (!(trunc->getType()->isIntegerTy(1) &&
                trunc->getOperand(0)->getType()->isIntegerTy(8) &&
                isa<LoadInst>(trunc->getOperand(0)))) {
            ++I;
            continue;
          }

          ++I;
          B.SetInsertPoint(trunc);
          Value *v = B.CreateICmpSGT(trunc->getOperand(0), B.getInt8(0));
          if (Instruction *inst = dyn_cast<Instruction>(v))
            inst->setDebugLoc(trunc->getDebugLoc());
          trunc->replaceAllUsesWith(v);
          trunc->eraseFromParent();
          changed = true;
        } else
          ++I;
      }
    }

    return changed;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const { AU.setPreservesAll(); }
};

char PromoteBoolLoads::ID = 0;
} // namespace

namespace seahorn {
Pass *createPromoteBoolLoadsPass() { return new PromoteBoolLoads(); }
} // namespace seahorn

static llvm::RegisterPass<PromoteBoolLoads> X("promote-bools",
                                              "Promote _Bool loads");
