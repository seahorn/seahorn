//===-------- Resolve indirect calls using type signatures ----------------===//
//
// Resolve the targets of an indirect call by selecting all functions
// whose signatures match.
//
//===----------------------------------------------------------------------===//

#include "seahorn/Transforms/Utils/DevirtFunctions.hh"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

using namespace llvm;

static llvm::cl::opt<bool>
    AllowIndirectCalls("allow-indirect-calls",
                       llvm::cl::desc("Allow creation of indirect calls "
                                      "during devirtualization "
                                      "(required for soundness)"),
                       llvm::cl::init(false));

namespace seahorn {

//  Currently, only type information is used to resolve indirect
//  calls. In the future, we can combined with other resolvers such
//  as: alias-based, CHA-based for C++, etc.
class DevirtualizeFunctionsPass : public ModulePass {
public:
  static char ID;

  DevirtualizeFunctionsPass() : ModulePass(ID) {}

  virtual bool runOnModule(Module &M) {
    // -- Get the call graph
    CallGraph *CG = &(getAnalysis<CallGraphWrapperPass>().getCallGraph());
    DevirtualizeFunctions DF(CG);
    // -- Choose the callsite resolver by types
    CallSiteResolverByTypes typesCSR(M);
    CallSiteResolver *CSR = &typesCSR;
    // -- Resolve all the indirect calls
    bool res = DF.resolveCallSites(M, CSR, AllowIndirectCalls);
    return res;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<CallGraphWrapperPass>();
    AU.setPreservesAll();
    AU.addPreserved<CallGraphWrapperPass>();
  }

  StringRef getPassName() const {
    return "DevirtualizeFunctions (considering only types)";
  }
};

char DevirtualizeFunctionsPass::ID = 0;

Pass *createDevirtualizeFunctionsPass() {
  return new DevirtualizeFunctionsPass();
}

} // namespace seahorn

// Pass registration
static RegisterPass<seahorn::DevirtualizeFunctionsPass>
    XX("devirt-functions",
       "Devirtualize indirect function calls using only types");
