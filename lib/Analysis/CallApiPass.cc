#include "seahorn/Analysis/CallApiPass.hh"

/**
* Identifies functions that call a specific API function
*/
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "avy/AvyDebug.h"



namespace seahorn
{
  using namespace llvm;

  // The body of the pass
  bool CallApiPass::runOnModule (Module &M)
  {
    errs() << "Running analysis on called APIs, looking for " << m_apiname << "\n";;

    for (Function &F : M)
    {
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)
      {
        Instruction *I = &*i;
        if (const CallInst *CI = dyn_cast<CallInst> (I))
        {
          CallSite CS (const_cast<CallInst*> (CI));
          const Function *cf = CS.getCalledFunction ();

          if (cf) {

            if (cf->getName().str().find (m_apiname) != std::string::npos)  {
              errs() << "Found a call!\n";
              m_callsapi.insert (&F);
            }
          }
        }
      }
    }

    errs () << "Calls API: " << m_apiname << "\n";
    for (auto v : m_callsapi) errs () << v->getName () << ", ";
    errs () << "\n";

    return false;
  }

  void CallApiPass::getAnalysisUsage (AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  }

  char CallApiPass::ID = 0;

  llvm::Pass *createCallApiPass(std::string &config) {
    return new CallApiPass(config);
  }

  llvm::Pass *createCallApiPass() {
    return new CallApiPass();
  }

}   // namespace seahorn

static llvm::RegisterPass<seahorn::CallApiPass>
X("call-api", "Determine if a given API is called",false, false);
