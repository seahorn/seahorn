#ifndef _CALL_API_PASS_HH_
#define _CALL_API_PASS_HH_

/**
* Identifies functions that call a specific API function
*/

#include <sstream>

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
    std::set< std::pair<const Function*, std::string> > m_apicalllist;

    // The API name to look for
    std::vector<std::string> m_apis;

    size_t m_progress;

    void parseApiString(std::string apistring);

  public:
    static char ID;

    CallApiPass () : ModulePass (ID), m_progress(0) { }

    CallApiPass (std::string &apistring) : ModulePass (ID), m_progress(0) {
      parseApiString(apistring);
    }

    virtual bool runOnModule (Module &M);

    virtual void getAnalysisUsage (AnalysisUsage &AU) const;

    virtual const char* getPassName () const { return "CallApiPass"; }
  };
}
#endif /* _CALL_API_PASS_HH_ */
