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
#include "avy/AvyDebug.h"
#include "seahorn/Support/SortTopo.hh"
#include "llvm/ADT/PostOrderIterator.h"

namespace seahorn
{
  using namespace llvm;

  typedef std::pair<const BasicBlock*, unsigned int> BBApiEntry;

  // Each Basic block in a function will have an ApiCallList
  typedef std::vector<BBApiEntry> BBApiList;

  struct ApiCallInfo {

    ApiCallInfo()
    { }

    ApiCallInfo(const ApiCallInfo & other)
    {
      m_bblist = other.m_bblist;
      m_func = other.m_func;
    }

    ApiCallInfo& operator=(const ApiCallInfo & other)
    {
      m_bblist = other.m_bblist;
      m_func = other.m_func;

      return *this;
    }

    BBApiEntry& getFinalAnalysis()
    {
      return m_bblist.back();
    }

    // data flow information for each basic block in this function
    BBApiList m_bblist;

    // A pointer to the function itself
    const Function* m_func;

    std::vector< std::string> m_path;

    // APIs in this function in the order encountered
    std::vector<std::string> m_apiSeq;
  };

  class ApiAnalysisPass : public ModulePass
  {
    // functions/instructions that call an API of interest
    std::set< std::pair<const Function*, std::string> > m_apicalllist;

    // The API name to look for
    std::vector<std::string> m_apilist;

    // Dataflow analysis for each function
    std::vector<ApiCallInfo> m_apiAnalysis;

    void parseApiString(std::string apistring);

    void analyze(const Function *F, unsigned int& progress, ApiCallInfo& aci);

    void report();

  public:

    static char ID;

    ApiAnalysisPass () : ModulePass (ID)
    { }

    ApiAnalysisPass (std::string &apistring) : ModulePass (ID)
    {
      parseApiString(apistring);
    }

    virtual bool runOnModule (Module &M);

    virtual void getAnalysisUsage (AnalysisUsage &AU) const;

    virtual const char* getPassName () const
    { return "ApiAnalysisPass"; }
  };
}
#endif /* _CALL_API_PASS_HH_ */
