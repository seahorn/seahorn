#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/range.hpp"
#include "seahorn/Support/SeaDebug.h"

using namespace llvm;

namespace seahorn {

struct LowerLibCxxAbiFunctions : public ModulePass {
  static char ID;

  Function *m_mallocFn;
  Function *m_freeFn;

  LowerLibCxxAbiFunctions() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {

    LLVMContext &Context = M.getContext();
    AttrBuilder B(Context);
    AttributeList as =
        AttributeList::get(Context, AttributeList::FunctionIndex, B);

    const DataLayout *DL = &M.getDataLayout();
    Type *IntPtrTy = DL->getIntPtrType(Context, 0);

    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
    CallGraph *cg = cgwp ? &cgwp->getCallGraph() : nullptr;

    m_mallocFn = dyn_cast<Function>(M.getOrInsertFunction(
                                                          "malloc", as, Type::getInt8Ty(Context)->getPointerTo(), IntPtrTy).getCallee());

    if (cg)
      cg->getOrInsertFunction(m_mallocFn);

    m_freeFn = dyn_cast<Function>(
        M.getOrInsertFunction("free", as, Type::getVoidTy(Context),
                              Type::getInt8Ty(Context)->getPointerTo()).getCallee());

    if (cg)
      cg->getOrInsertFunction(m_freeFn);

    for (auto &F : M)
      runOnFunction(F);

    return true;
  }

  bool runOnFunction(Function &F) {

    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
    CallGraph *cg = cgwp ? &cgwp->getCallGraph() : nullptr;

    SmallVector<Instruction *, 16> toKill;

    bool Changed = false;
    for (auto &I : boost::make_iterator_range(inst_begin(F), inst_end(F))) {
      if (!isa<CallInst>(&I))
        continue;

      // // -- look through pointer casts
      // Value *v = I.stripPointerCasts ();
      auto &CI = cast<CallInst>(I);
      const Function *fn = CI.getCalledFunction();

      // -- check if this is a call through a pointer cast
      if (!fn && CI.getCalledOperand())
        fn = dyn_cast<const Function>(CI.getCalledOperand()->stripPointerCasts());

      if (fn && (fn->getName().equals("__cxa_allocate_exception") ||
                 fn->getName().equals("__cxa_allocate_dependent_exception"))) {
        if (CI.doesNotReturn() || CI.data_operands_size() != 1)
          continue;

        IRBuilder<> Builder(F.getContext());
        Builder.SetInsertPoint(&I);
        CallInst *ci = Builder.CreateCall(m_mallocFn, CI.getOperand(0));
        ci->setDebugLoc(I.getDebugLoc());
        if (cg)
          (*cg)[&F]->addCalledFunction(ci,
                                       (*cg)[ci->getCalledFunction()]);

        LOG("lower-libc++abi",
            errs() << "Replaced " << I << " with " << *ci << "\n");

        I.replaceAllUsesWith(ci);
        toKill.push_back(&I);

      } else if (fn &&
                 (fn->getName().equals("__cxa_free_exception") ||
                  fn->getName().equals("__cxa_free_dependent_exception"))) {
        if (!CI.doesNotReturn() || CI.arg_size() != 1)
          continue;

        IRBuilder<> Builder(F.getContext());
        Builder.SetInsertPoint(&I);
        CallInst *ci = Builder.CreateCall(m_freeFn, CI.getOperand(0));
        ci->setDebugLoc(I.getDebugLoc());

        LOG("lower-libc++abi",
            errs() << "Replaced " << I << " with " << *ci << "\n");

        if (cg)
          (*cg)[&F]->addCalledFunction(ci,
                                       (*cg)[ci->getCalledFunction()]);
        toKill.push_back(&I);
      } else if (fn && fn->getName().equals("__cxa_throw")) {
        LOG("lower-libc++abi", errs() << "Deleted " << I << "\n");
        // Assume that after this call there is always an
        // unreachable instruction
        toKill.push_back(&I);
      }
    }

    for (auto *I : toKill)
      I->eraseFromParent();

    return Changed;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
    AU.addRequired<llvm::CallGraphWrapperPass>();
  }

  virtual StringRef getPassName() const override {
    return "Lower Libc++abi functions";
  }
};

char LowerLibCxxAbiFunctions::ID = 0;

Pass *createLowerLibCxxAbiFunctionsPass() {
  return new LowerLibCxxAbiFunctions();
}

} // namespace seahorn
