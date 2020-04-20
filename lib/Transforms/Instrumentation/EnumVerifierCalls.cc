#define DEBUG_TYPE "enum-verifier-calls"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

namespace {
/// Duplicate each callsite to verifier.error with a new call to
/// seahorn.error(id) where id is an unique identifier for the
/// callsite.
class EnumVerifierCalls : public ModulePass {
  FunctionCallee m_errorFn;
  unsigned int m_id;

public:
  static char ID;

  EnumVerifierCalls() : ModulePass(ID), m_errorFn(nullptr), m_id(0) {}

  virtual bool runOnModule(Module &M) {

    m_errorFn =
        M.getOrInsertFunction("seahorn.error", Type::getVoidTy(M.getContext()),
                              Type::getInt32Ty(M.getContext()));

    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
    if (CallGraph *cg = cgwp ? &cgwp->getCallGraph() : nullptr) {
      cg->getOrInsertFunction(cast<Function>(m_errorFn.getCallee()));
    }

    bool change = false;
    for (auto &F : M)
      change |= runOnFunction(F);

    return change;
  }

  virtual bool runOnFunction(Function &F) {
    if (F.empty())
      return false;

    IRBuilder<> Builder(F.getContext());

    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
    CallGraph *cg = cgwp ? &cgwp->getCallGraph() : nullptr;

    std::vector<CallInst *> Worklist;
    for (auto &BB : F)
      for (auto &I : BB) {
        CallInst *CI = dyn_cast<CallInst>(&I);
        if (!CI)
          continue;
        Function *CF = CI->getCalledFunction();
        if (!CF)
          continue;
        if (CF->getName().equals("verifier.error"))
          Worklist.push_back(CI);
      }

    if (Worklist.empty())
      return false;

    while (!Worklist.empty()) {
      CallInst *CI = Worklist.back();
      Worklist.pop_back();

      Function *CF = CI->getCalledFunction();

      Builder.SetInsertPoint(CI);
      CallInst *call = Builder.CreateCall(
          m_errorFn,
          ConstantInt::get(Type::getInt32Ty(F.getContext()), m_id++));
      call->setDebugLoc(CI->getDebugLoc());
      if (cg)
        (*cg)[&F]->addCalledFunction(call,
                                     (*cg)[call->getCalledFunction()]);
    }

    return true;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<CallGraphWrapperPass>();
  }
};

char EnumVerifierCalls::ID = 0;
} // namespace

namespace seahorn {
llvm::Pass *createEnumVerifierCallsPass() { return new EnumVerifierCalls(); }
} // namespace seahorn

static RegisterPass<EnumVerifierCalls>
    X("enum-verifier-calls",
      "Assign unique identifiers to each call to verifier.error");
