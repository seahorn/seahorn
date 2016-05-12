#ifndef _CALL_API_PASS_HH_
#define _CALL_API_PASS_HH_

/**
* Identifies functions that call a specific API function
*/

#include <sstream>
#include <boost/ptr_container/ptr_vector.hpp>

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

  //typedef std::pair<std::string, bool> ApiEntry;

  // This is a list of expected API entries
  typedef std::vector<std::string> ApiCallList;

  typedef std::pair<const BasicBlock*, ApiCallList> BBApiEntry;

  // Each Basic block in a function will have an ApiCallList
  //typedef std::vector<BBApiEntry> BBApiList;

  // information about a serach
  struct ApiCallInfo
  {
    ApiCallInfo() : m_progress(0)
    { }

    ~ApiCallInfo()
    { }

    ApiCallInfo(const ApiCallInfo & other)
    {
      m_funcs = other.m_funcs;
      m_progress = other.m_progress;
      m_finalapilist = other.m_finalapilist;
      m_startFunc = other.m_startFunc;
    }

    ApiCallInfo& operator=(const ApiCallInfo & other)
    {
      m_funcs = other.m_funcs;
      m_progress = other.m_progress;
      m_finalapilist = other.m_finalapilist;
      m_startFunc = other.m_startFunc;

      return *this;
    }

    // data flow information for each basic block in this function. Needed for
    // sequencing
    //BBApiList m_bblist;

    ApiCallList m_finalapilist;

    unsigned int m_progress;

    // List of functions traversed
    std::vector<Function*> m_funcs;

    // Function containing the first API of interest
    Function * m_startFunc;
  };


  class ApiAnalysisPass : public ModulePass
  {
    // The API name to look for
    std::vector<std::string> m_apilist;

    // Dataflow analysis for a given search
    boost::ptr_vector<ApiCallInfo> m_apiAnalysis;

    ApiCallList initializeApiCallList();

    void parseApiString(std::string apistring);

    ApiCallInfo* analyzeFunction(Function& F, ApiCallInfo *init_state);

    void printFinalAnalysis() const;

  public:

    static char ID;

    ~ApiAnalysisPass()
    {
      //m_apiAnalysis.clear();
    }

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
