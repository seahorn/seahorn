#include "llvm/ADT/SmallVector.h"
#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"

#include "seahorn/Support/SeaDebug.h"

using namespace llvm;

#define DEBUG_TYPE "symbolize-bounds"

STATISTIC(SymbolizedLoops,
          "Number of constant loop bounds converted to symbolic bounds");

namespace {
/*
   Transform loops with constant bounds

   foo (...) {
     ...
     for (int i=start ;i < 500; i+=k)
     { ... }
   }

   into symbolic loops of this form

   foo (...) {
     int n = nd ();
     assume (n == 500);
     ....
     for (int i=start ;i < n; i+=k)
     { ... }
   }
 */
class SymbolizeConstantLoopBounds : public FunctionPass {

  Function *assumeFn;
  Function *nondetFn;
  CallGraph *cg;

  void updateCallGraph(Function *caller, CallInst *callee) {
    if (cg) {
      (*cg)[caller]->addCalledFunction(callee,
                                       (*cg)[callee->getCalledFunction()]);
    }
  }

  Instruction *getLoopExitCond(BasicBlock *ExitingLoop) {
    auto *TI = ExitingLoop->getTerminator();
    if (BranchInst *BI = dyn_cast<BranchInst>(TI)) {
      if (BI->isConditional()) {
        return dyn_cast<Instruction>(BI->getCondition());
      }
    }
    return nullptr;
  }

  bool SymbolizeInst(Instruction *I, IRBuilder<> &B) {

    if (I->getOpcode() == BinaryOperator::And ||
        I->getOpcode() == BinaryOperator::Or ||
        I->getOpcode() == BinaryOperator::Xor) {
      bool Change = false;
      if (Instruction *I1 = dyn_cast<Instruction>(I->getOperand(0)))
        Change |= SymbolizeInst(I1, B);
      if (Instruction *I2 = dyn_cast<Instruction>(I->getOperand(1)))
        Change |= SymbolizeInst(I2, B);
      return Change;
    } else if (CmpInst *CI = dyn_cast<CmpInst>(I)) {

      Value *Op1 = CI->getOperand(0);
      Value *Op2 = CI->getOperand(1);
      Function *F = CI->getParent()->getParent();

      // Assume that only one operand can be constant
      Value *CstBound = nullptr;
      if (ConstantInt *C = dyn_cast<ConstantInt>(Op1)) {
        if (C->getBitWidth() > 1) // no booleans
          CstBound = Op1;
      } else if (ConstantInt *C = dyn_cast<ConstantInt>(Op2)) {
        if (C->getBitWidth() > 1) // no booleans
          CstBound = Op2;
      }

      if (!CstBound) {
        LOG("sym-bound",
            errs() << "STC: no non-boolean integer constant operands\n");
        return false;
      }

      CallInst *nd = B.CreateCall(nondetFn, None, "loop.bound");
      Value *symBound = B.CreateSExtOrTrunc(nd, CstBound->getType());
      updateCallGraph(F, nd);
      CallInst *assumption =
          B.CreateCall(assumeFn, B.CreateICmpEQ(symBound, CstBound));
      updateCallGraph(F, assumption);

      // --- replace the constant bound with the symbolic one.
      //     We could replace any occurrence of the constant bound
      //     inside the loop or even the function.
      LOG("sym-bound", errs() << "STC: replaced " << *CI << " with ");
      if (CI->getOperand(0) == CstBound) {
        CI->setOperand(0, symBound);
      } else {
        CI->setOperand(1, symBound);
      }
      LOG("sym-bound", errs() << *CI << "\n");

      SymbolizedLoops++;
      return true;
    }
    return false;
  }

  bool SymbolizeLoop(Loop *L, IRBuilder<> &B) {
    LOG("sym-bound", errs() << "STC:" << *L << "\n");
    bool Change = false;
    SmallVector<BasicBlock *, 16> ExitingBlocks;
    L->getExitingBlocks(ExitingBlocks);
    for (BasicBlock *ExitingBlock : ExitingBlocks) {
      Instruction *ExitCond = getLoopExitCond(ExitingBlock);
      if (!ExitCond) {
        LOG("sym-bound", errs()
                             << "STC: Skipped exiting block " << *ExitingBlock
                             << " because no condition found\n");
        continue;
      }

      LOG("sym-bound",
          errs() << "STC: found loop condition " << *ExitCond << "\n");

      Change |= SymbolizeInst(ExitCond, B);
    }
    return Change;
  }

public:
  static char ID;

  SymbolizeConstantLoopBounds() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override {
    if (F.isDeclaration() || F.empty())
      return false;

    Module *M = F.getParent();
    LLVMContext &ctx = M->getContext();
    Type *voidTy = Type::getVoidTy(ctx);
    Type *boolTy = Type::getInt1Ty(ctx);

    const DataLayout *dl = &(M->getDataLayout());
    Type *intTy = dl->getIntPtrType(ctx, 0);

    IRBuilder<> B(ctx);
    BasicBlock::iterator insertPt = F.getEntryBlock().getFirstInsertionPt();
    B.SetInsertPoint(&*insertPt);

    AttrBuilder AB(ctx);
    AttributeList as =
        AttributeList::get(ctx, AttributeList::FunctionIndex, AB);

    assumeFn = dyn_cast<Function>(
        M->getOrInsertFunction("verifier.assume", as, voidTy, boolTy)
            .getCallee());

    nondetFn = dyn_cast<Function>(
        M->getOrInsertFunction("verifier.nondet.sym.bound", as, intTy)
            .getCallee());

    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
    cg = cgwp ? &cgwp->getCallGraph() : nullptr;
    if (cg) {
      cg->getOrInsertFunction(assumeFn);
      cg->getOrInsertFunction(nondetFn);
    }

    LoopInfo *LI = &getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
    bool Change = false;
    for (auto *L : *LI) {
      // symbolize nested loops
      for (auto SL : *L) {
        Change |= SymbolizeLoop(SL, B);
      }
      // symbolize outermost loop
      Change |= SymbolizeLoop(L, B);
    }

    if (Change) {
      // -- HOOK: we insert an empty loop "while(nd()){}" between
      //    entry and succ.  The reason for that is to enforce that
      //    the initialization of the loop bounds and the loop
      //    conditions where those bounds are used go to different
      //    cutpoint graphs during the VC encoding phase.

      BasicBlock &entry = F.getEntryBlock();
      if (BranchInst *BI = dyn_cast<BranchInst>(entry.getTerminator())) {
        if (BI->isUnconditional()) {
          // TODO: update LoopInfo
          BasicBlock *succ = BI->getSuccessor(0);
          BasicBlock *header = BasicBlock::Create(ctx, "empty.loop", &F);
          BasicBlock *body = BasicBlock::Create(ctx, "empty.loop.body", &F);
          entry.replaceSuccessorsPhiUsesWith(header);
          B.SetInsertPoint(body);
          B.CreateBr(header);
          B.SetInsertPoint(header);
          Function *fn = dyn_cast<Function>(
              M->getOrInsertFunction("verifier.nondet.bool", as, boolTy)
                  .getCallee());
          B.CreateCondBr(B.CreateCall(fn, None, "nd.loop.cond"), body, succ);
          BI->eraseFromParent();
          B.SetInsertPoint(&entry);
          B.CreateBr(header);
        }
      }
    }
    return Change;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    AU.addRequired<LoopInfoWrapperPass>();
    AU.addRequired<llvm::CallGraphWrapperPass>();
  }

  virtual StringRef getPassName() const override {
    return "Convert constant loop bounds into symbolic bounds";
  }
};

char SymbolizeConstantLoopBounds::ID = 0;
} // namespace

namespace seahorn {
Pass *createSymbolizeConstantLoopBoundsPass() {
  return new SymbolizeConstantLoopBounds();
}
} // namespace seahorn

static llvm::RegisterPass<SymbolizeConstantLoopBounds>
    X("symbolize-constant-loop-bounds",
      "Convert constant loop bounds into symbolic");
