#include "seahorn/Transforms/Scalar/PromoteVerifierCalls.hh"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"

#include "llvm/IR/IRBuilder.h"

#include "boost/range.hpp"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"

#include "llvm/Analysis/CallGraph.h"
using namespace llvm;

namespace seahorn {
char PromoteVerifierCalls::ID = 0;

bool PromoteVerifierCalls::runOnModule(Module &M) {
  LOG("pvc", errs() << "Running promote-verifier-calls pass\n";);

  LLVMContext &Context = M.getContext();

  AttrBuilder B;

  AttributeList as =
      AttributeList::get(Context, AttributeList::FunctionIndex, B);

  m_assumeFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.assume", as, Type::getVoidTy(Context),
                            Type::getInt1Ty(Context)));

  Function *assumeNotFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.assume.not", as, Type::getVoidTy(Context),
                            Type::getInt1Ty(Context)));

  m_assertFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.assert", as, Type::getVoidTy(Context),
                            Type::getInt1Ty(Context)));

  m_failureFn = dyn_cast<Function>(
      M.getOrInsertFunction("seahorn.fail", as, Type::getVoidTy(Context)));

  B.addAttribute(Attribute::NoReturn);
  // XXX LLVM optimizer removes ReadNone functions even if they do not return!
  // B.addAttribute (Attribute::ReadNone);

  as = AttributeList::get(Context, AttributeList::FunctionIndex, B);
  m_errorFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.error", as, Type::getVoidTy(Context)));

  /* add our functions to llvm used */
  GlobalVariable *LLVMUsed = M.getGlobalVariable("llvm.used");
  std::vector<Constant *> MergedVars;
  if (LLVMUsed) {
    // Collect the existing members of llvm.used except sea
    // functions
    ConstantArray *Inits = cast<ConstantArray>(LLVMUsed->getInitializer());
    for (unsigned I = 0, E = Inits->getNumOperands(); I != E; ++I) {
      Value *V = Inits->getOperand(I)->stripPointerCasts();
      MergedVars.push_back(Inits->getOperand(I));
    }
    LLVMUsed->eraseFromParent();
  }
  // re-create llvm.used
  Type *i8PTy = Type::getInt8PtrTy(M.getContext());
  MergedVars.push_back(
      ConstantExpr::getBitCast(cast<llvm::Constant>(m_assumeFn), i8PTy));
  MergedVars.push_back(
      ConstantExpr::getBitCast(cast<llvm::Constant>(assumeNotFn), i8PTy));
  MergedVars.push_back(
      ConstantExpr::getBitCast(cast<llvm::Constant>(m_errorFn), i8PTy));
  MergedVars.push_back(
      ConstantExpr::getBitCast(cast<llvm::Constant>(m_failureFn), i8PTy));
  ArrayType *ATy = ArrayType::get(i8PTy, MergedVars.size());
  LLVMUsed = new llvm::GlobalVariable(
      M, ATy, false, llvm::GlobalValue::AppendingLinkage,
      llvm::ConstantArray::get(ATy, MergedVars), "llvm.used");
  LLVMUsed->setSection("llvm.metadata");

  CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
  if (CallGraph *cg = cgwp ? &cgwp->getCallGraph() : nullptr) {
    cg->getOrInsertFunction(m_assumeFn);
    cg->getOrInsertFunction(m_assertFn);
    cg->getOrInsertFunction(m_errorFn);
    cg->getOrInsertFunction(m_failureFn);
  }

  for (auto &F : M)
    runOnFunction(F);
  return true;
}

bool PromoteVerifierCalls::runOnFunction(Function &F) {
  CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
  CallGraph *cg = cgwp ? &cgwp->getCallGraph() : nullptr;

  SmallVector<Instruction *, 16> toKill;

  bool Changed = false;
  for (auto &I : boost::make_iterator_range(inst_begin(F), inst_end(F))) {
    if (!isa<CallInst>(&I))
      continue;

    // // -- look through pointer casts
    // Value *v = I.stripPointerCasts ();
    // CallSite CS (const_cast<Value*> (v));

    CallSite CS(&I);
    const Function *fn = CS.getCalledFunction();

    // -- check if this is a call through a pointer cast
    if (!fn && CS.getCalledValue())
      fn = dyn_cast<const Function>(CS.getCalledValue()->stripPointerCasts());

    if (fn && (fn->getName().equals("__VERIFIER_assume") ||
               fn->getName().equals("DISABLED__VERIFIER_assert") ||
               /** pagai embedded invariants */
               fn->getName().equals("llvm.invariant") ||
               /** my suggested name for pagai invariants */
               fn->getName().equals("pagai.invariant"))) {
      Function *nfn;
      if (fn->getName().equals("__VERIFIER_assume"))
        nfn = m_assumeFn;
      else if (fn->getName().equals("llvm.invariant"))
        nfn = m_assumeFn;
      else if (fn->getName().equals("pagai.invariant"))
        nfn = m_assumeFn;
      else if (fn->getName().equals("__VERIFIER_assert"))
        nfn = m_assertFn;
      else
        continue;

      Value *cond = CS.getArgument(0);

      // strip zext if there is one
      if (const ZExtInst *ze = dyn_cast<const ZExtInst>(cond))
        cond = ze->getOperand(0);

      IRBuilder<> Builder(F.getContext());
      Builder.SetInsertPoint(&I);

      // -- convert to Boolean if needed
      if (!cond->getType()->isIntegerTy(1))
        cond = Builder.CreateICmpNE(cond, ConstantInt::get(cond->getType(), 0));

      CallInst *ci = Builder.CreateCall(nfn, cond);
      if (cg)
        (*cg)[&F]->addCalledFunction(CallSite(ci),
                                     (*cg)[ci->getCalledFunction()]);

      toKill.push_back(&I);
    } else if (fn && fn->getName().equals("__VERIFIER_error")) {
      IRBuilder<> Builder(F.getContext());
      Builder.SetInsertPoint(&I);
      CallInst *ci = Builder.CreateCall(m_errorFn);
      ci->setDebugLoc(I.getDebugLoc());
      if (cg)
        (*cg)[&F]->addCalledFunction(CallSite(ci),
                                     (*cg)[ci->getCalledFunction()]);

      toKill.push_back(&I);
    } else if (fn && (fn->getName().equals("__SEAHORN_fail") ||
                      /* map __llbmc_assert to seahorn.fail to support legacy
                         frontend */
                      fn->getName().equals("__llbmc_assert"))) {
      Function *main = F.getParent()->getFunction("main");
      if (!main || main != &F) {
        errs() << "__SEAHORN_fail can only be called from the main function.\n";
        return false;
      }

      IRBuilder<> Builder(F.getContext());
      Builder.SetInsertPoint(&I);
      CallInst *ci = Builder.CreateCall(m_failureFn);
      ci->setDebugLoc(I.getDebugLoc());
      if (cg)
        (*cg)[&F]->addCalledFunction(CallSite(ci),
                                     (*cg)[ci->getCalledFunction()]);

      toKill.push_back(&I);
    }
  }

  for (auto *I : toKill)
    I->eraseFromParent();

  return Changed;
}

void PromoteVerifierCalls::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

} // namespace seahorn
namespace seahorn {
Pass *createPromoteVerifierClassPass() { return new PromoteVerifierCalls(); }
} // namespace seahorn

static llvm::RegisterPass<seahorn::PromoteVerifierCalls>
    X("promote-verifier", "Promote all verifier related function");
