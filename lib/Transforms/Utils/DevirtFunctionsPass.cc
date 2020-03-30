//===-------- Resolve indirect calls using type signatures ----------------===//
//
// Resolve the targets of an indirect call by selecting all functions
// whose signatures match.
//
//===----------------------------------------------------------------------===//

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Transforms/Utils/DevirtFunctions.hh"

#include "llvm/ADT/StringRef.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"

#include "sea_dsa/AllocWrapInfo.hh"
#include "sea_dsa/CompleteCallGraph.hh"

static llvm::cl::opt<seahorn::CallSiteResolverKind>
Devirt("devirt-functions-method",
      llvm::cl::desc ("Method used to devirtualize (resolve) indirect calls"),
      llvm::cl::values 
       (clEnumValN(seahorn::CallSiteResolverKind::RESOLVER_TYPES, "types",
		  "Choose all possible functions with same type signature"),
       clEnumValN(seahorn::CallSiteResolverKind::RESOLVER_SEA_DSA  , "sea-dsa",
		  "Sea-Dsa selects the potential callees "
		  "after discarding those with inconsistent types")),
      llvm::cl::init(seahorn::CallSiteResolverKind::RESOLVER_TYPES));

static llvm::cl::opt<bool>
UseCHA("devirt-functions-with-cha",
       llvm::cl::desc("Resolve indirect calls by using CHA. "
		      "This is prior to run --devirt "
		      "(useful for C++ programs)"),
       llvm::cl::init(false));

static llvm::cl::opt<bool>
AllowIndirectCalls("devirt-functions-allow-indirect-calls",
      llvm::cl::desc("Allow creation of indirect calls "
		     "during devirtualization "
		     "(required for soundness)"),
      llvm::cl::Hidden,
      llvm::cl::init(false));

static llvm::cl::opt<bool>
AllowIncompleteDsaNodes("devirt-functions-allow-incomplete",
      llvm::cl::desc("Allow the use of incomplete dsa nodes to resolve calls. "
		     "This is potentially unsound."),
      llvm::cl::Hidden,
      llvm::cl::init(false));


namespace seahorn {

using namespace llvm;

class DevirtualizeFunctionsPass : public ModulePass {
public:
  static char ID;

  DevirtualizeFunctionsPass() : ModulePass(ID) {}

  virtual bool runOnModule(Module &M) {
    // -- Get the call graph to update
    CallGraph &cg = getAnalysis<CallGraphWrapperPass>().getCallGraph();
    DevirtualizeFunctions DF(&cg, AllowIndirectCalls);
    bool res = false;

    if (UseCHA) {
      // We first run CHA to resolve as many C++ calls as possible by
      // looking at the virtual tables.
      LOG("devirt", errs() << "Devirtualizing first indirect calls using CHA ...\n";);
      CallSiteResolverByCHA csr_cha(M);
      res |= DF.resolveCallSites(M, &csr_cha);
    }
    
    std::unique_ptr<CallSiteResolver> CSR;
    switch(Devirt) {
    case CallSiteResolverKind::RESOLVER_TYPES: {
      LOG("devirt", errs() << "Devirtualizing indirect calls using types ...\n";);
      CSR.reset(new CallSiteResolverByTypes(M));
      res |= DF.resolveCallSites(M, &*CSR);
      break;
    }
    case CallSiteResolverKind::RESOLVER_SEA_DSA: {
      LOG("devirt", errs() << "Devirtualizing indirect calls using sea-dsa+types ...\n";);
      auto &dl = M.getDataLayout();
      auto &tli = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
      auto &allocInfo = getAnalysis<sea_dsa::AllocWrapInfo>();
      sea_dsa::CompleteCallGraphAnalysis ccga(dl, tli, allocInfo, cg, true);
      ccga.runOnModule(M);
      LOG("devirt-dsa-cg", ccga.printStats(M, errs()));
      CSR.reset(new CallSiteResolverByDsa(M, ccga, AllowIncompleteDsaNodes));
      res |= DF.resolveCallSites(M, &*CSR);
      break;
    }
    default:;;
    }  
    return res;
  }

  virtual void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<CallGraphWrapperPass>();
    AU.setPreservesAll();
    AU.addPreserved<CallGraphWrapperPass>();
      
    if (Devirt == CallSiteResolverKind::RESOLVER_SEA_DSA) {
      AU.addRequired<TargetLibraryInfoWrapperPass>();
      AU.addRequired<sea_dsa::AllocWrapInfo>();      
    }
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
