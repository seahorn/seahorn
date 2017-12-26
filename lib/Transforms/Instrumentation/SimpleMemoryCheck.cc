#include "seahorn/Transforms/Instrumentation/SimpleMemoryCheck.hh"

#include "llvm/ADT/DenseMap.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "avy/AvyDebug.h"
#include "sea_dsa/DsaAnalysis.hh"

#define SMC_LOG(...) LOG("smc", __VA_ARGS__)

using namespace llvm;

namespace seahorn {

class SimpleMemoryCheck : public llvm::ModulePass {
public:
  static char ID;
  SimpleMemoryCheck() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual const char *getPassName() const { return "SimpleMemoryCheck"; }

private:
};

llvm::ModulePass *CreateSimpleMemoryCheckPass() {
  return new SimpleMemoryCheck();
}

bool SimpleMemoryCheck::runOnModule(llvm::Module &M) {
  return true;
}

void SimpleMemoryCheck::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<sea_dsa::DsaInfoPass>(); // run seahorn dsa
  AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
  AU.addRequired<llvm::UnifyFunctionExitNodes>();
  AU.addRequired<llvm::CallGraphWrapperPass>();
  // for debugging
  // AU.addRequired<ufo::NameValues> ();
}

char SimpleMemoryCheck::ID = 0;

static llvm::RegisterPass<SimpleMemoryCheck>
    Y("smc", "Insert array buffer checks using simple encoding");

} // end namespace seahorn
