#ifndef _CALL_API_PASS_HH_
#define _CALL_API_PASS_HH_

/**
 * Identifies functions that call a specific API function
 */
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SetVector.h"

namespace seahorn
{

  using namespace llvm;

  class CallApiPass : public ModulePass
  {
    /// functions/instructions that call an API of interest
    DenseSet<const Function*> m_callsapi;

    // The API name to look for
    std::string m_apiname;

  public:
    static char ID;

    CallApiPass () : ModulePass (ID) { }

    CallApiPass (std::string &apiname) : ModulePass (ID) {



    }

    virtual bool runOnModule (Module &M);

    virtual void getAnalysisUsage (AnalysisUsage &AU) const;

    virtual const char* getPassName () const { return "CallApiPass"; }
  };
}
#endif /* _CALL_API_PASS_HH_ */
