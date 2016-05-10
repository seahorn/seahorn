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

  typedef std::pair<std::string, bool> ApiEntry;

  // This is a list of expected API entries
  typedef std::vector<ApiEntry> ApiCallList;

  typedef std::pair<const BasicBlock*, ApiCallList> BBApiEntry;

  // Each Basic block in a function will have an ApiCallList
  typedef std::vector<BBApiEntry> BBApiList;

  // information about a serach
  struct ApiCallInfo
  {
    ApiCallInfo() : m_progress(0)
    { }

    ApiCallInfo(const ApiCallInfo & other)
    {
      m_bblist = other.m_bblist;
      m_func = other.m_func;
      m_outcalls = other.m_outcalls;
      m_progress = other.m_progress;
    }

    ApiCallInfo& operator=(const ApiCallInfo & other)
    {
      m_bblist = other.m_bblist;
      m_func = other.m_func;
      m_outcalls = other.m_outcalls;
      m_progress = other.m_progress;

      return *this;
    }

    BBApiEntry& getFinalAnalysis()
    {
      return m_bblist.back();
    }

    // data flow information for each basic block in this function
    BBApiList m_bblist;

    unsigned int m_progress;

    // A pointer to the function itself
    Function * m_func;

    // dataflow information for outgoing calls
    std::vector<Function*> m_outcalls;

  };


  class ApiAnalysisPass : public ModulePass
  {
    // functions/instructions that call an API of interest
    std::set< std::pair<const Function*, std::string> > m_apicalllist;

    // The API name to look for
    std::vector<std::string> m_apilist;

    // Dataflow analysis for a given search
    std::vector<ApiCallInfo> m_apiAnalysis;

    ApiCallList initializeApiCallList();

    void parseApiString(std::string apistring);

    void analyzeFunction(Function &F);

    void propagateAnalysis();

    void runInterFunctionAnalysis();

    void reportResults();



    void analyzeBBlock(const BasicBlock* bb);

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
