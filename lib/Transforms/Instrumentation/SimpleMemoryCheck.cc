#include "seahorn/Transforms/Instrumentation/SimpleMemoryCheck.hh"
#include "seahorn/Analysis/CanAccessMemory.hh"
#include "ufo/Passes/NameValues.hpp"

#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "boost/format.hpp"

// Seahorn dsa
#include "sea_dsa/DsaAnalysis.hh"
// Llvm dsa
#include "seahorn/Support/DSAInfo.hh"


namespace seahorn {

bool SimpleMemoryCheck::runOnModule(llvm::Module &M) {
  llvm::outs() << " ========== SMC  ==========\n";

  if (M.begin() == M.end())
    return false;

  Function *main = M.getFunction("main");
  if (!main) {
    errs() << "Main not found: no buffer overflow checks added\n";
    return false;
  }

  LLVMContext &ctx = M.getContext();

  const TargetLibraryInfo *tli =
      &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
  const DataLayout *dl = &M.getDataLayout();

  AttrBuilder AB;
  AB.addAttribute(Attribute::NoReturn);
  AttributeSet as = AttributeSet::get(ctx, AttributeSet::FunctionIndex, AB);
  Function *errorFn = dyn_cast<Function>(
      M.getOrInsertFunction("verifier.error", as, Type::getVoidTy(ctx), NULL));

  AB.clear();
  as = AttributeSet::get(ctx, AttributeSet::FunctionIndex, AB);
  Function *assumeFn = dyn_cast<Function>(M.getOrInsertFunction(
      "verifier.assume", as, Type::getVoidTy(ctx), Type::getInt1Ty(ctx), NULL));

  // Type *intPtrTy = dl->getIntPtrType (ctx, 0);
  // //errs () << "intPtrTy is " << *intPtrTy << "\n";
  // Type *i8PtrTy = Type::getInt8Ty (ctx)->getPointerTo ();

  IRBuilder<> B(ctx);

  CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass>();
  CallGraph *cg = cgwp ? &cgwp->getCallGraph() : nullptr;
  if (cg) {
    cg->getOrInsertFunction(assumeFn);
    cg->getOrInsertFunction(errorFn);
  }

  // unsigned untracked_dsa_checks = 0;
  SmallVector<Instruction *, 16> ToInstrument;
  // We instrument every address only once per basic block
  SmallSet<Value *, 16> TempsToInstrument;
  bool IsWrite;
  unsigned Aligment;


  errs() << " ========== SMC  ==========\n";
  // errs () << M << "\n";
  return true;
}

void SimpleMemoryCheck::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<seahorn::DSAInfo>();     // run llvm dsa
  AU.addRequired<sea_dsa::DsaInfoPass>(); // run seahorn dsa
  AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
  AU.addRequired<llvm::UnifyFunctionExitNodes>();
  AU.addRequired<llvm::CallGraphWrapperPass>();
  // for debugging
  // AU.addRequired<ufo::NameValues> ();
}

char SimpleMemoryCheck::ID = 0;

static llvm::RegisterPass<SimpleMemoryCheck>
    Y("abc-simple", "Insert array buffer checks using simple encoding");


} // end namespace seahorn
