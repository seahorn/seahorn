//===-------- Resolve indirect calls using type signatures ----------------===//
//
// Resolve the targets of an indirect call by selecting all functions
// whose signatures match.
//
//===----------------------------------------------------------------------===//

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Transforms/Utils/DevirtFunctions.hh"
#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

static llvm::cl::opt<bool>
    AllowIndirectCalls("allow-indirect-calls",
                       llvm::cl::desc("Allow creation of indirect calls "
                                      "during devirtualization "
                                      "(required for soundness)"),
                       llvm::cl::init(false));

static llvm::cl::opt<bool>
    ResolveCallsByCHA("devirt-functions-with-cha",
                      llvm::cl::desc("Resolve indirect calls by using CHA "
                                     "followed by types "
                                     "(useful for C++ programs)"),
                      llvm::cl::init(false));

namespace seahorn {

using namespace llvm;

class DevirtualizeFunctionsPass : public ModulePass {
public:
  static char ID;

  DevirtualizeFunctionsPass() : ModulePass(ID) {}

  virtual bool runOnModule(Module &M) {
    // -- Get the call graph
    CallGraph *CG = &(getAnalysis<CallGraphWrapperPass>().getCallGraph());
    DevirtualizeFunctions DF(CG);
    bool res = false;
    CallSiteResolver *CSR = nullptr;

    if (ResolveCallsByCHA) {
      LOG("devirt", errs() << "Devirtualizing indirect calls using CHA ...\n";);
      // -- Resolve all the indirect calls using CHA
      CallSiteResolverByCHA csr_cha(M);
      CSR = &csr_cha;
      res |= DF.resolveCallSites(M, CSR, AllowIndirectCalls);
    }

    LOG("devirt", errs() << "Devirtualizing indirect calls using types ...\n";);
    // -- Resolve the rest of indirect calls using types
    CallSiteResolverByTypes csr_types(M);
    CSR = &csr_types;
    res |= DF.resolveCallSites(M, CSR, AllowIndirectCalls);

    return res;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<CallGraphWrapperPass>();
    AU.setPreservesAll();
    AU.addPreserved<CallGraphWrapperPass>();
  }

  StringRef getPassName() const { return "DevirtualizeFunctions"; }
};

char DevirtualizeFunctionsPass::ID = 0;

Pass *createDevirtualizeFunctionsPass() {
  return new DevirtualizeFunctionsPass();
}

} // namespace seahorn

// Pass registration
static llvm::RegisterPass<seahorn::DevirtualizeFunctionsPass>
    XX("devirt-functions", "Devirtualize indirect function calls");
