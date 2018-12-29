#ifndef _CALL_API_PASS_HH_
#define _CALL_API_PASS_HH_

/**
* Identifies functions that call a specific API function
*/

#include <sstream>

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SetVector.h"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SortTopo.hh" 
#include "llvm/ADT/PostOrderIterator.h"

namespace seahorn
{
  using namespace llvm;

  struct ApiEntry
  {

    ApiEntry()
    { }

    ApiEntry(const BasicBlock* bb,unsigned int p,std::string f)
    : m_bb(bb), m_progress(p), m_func(f)
    { }

    ApiEntry(const ApiEntry& other)
    : m_bb(other.m_bb), m_progress(other.m_progress), m_func(other.m_func)
    { }

    const BasicBlock* m_bb;
    unsigned int m_progress;
    std::string m_func;
  };

  // Each Basic block in a function will have an ApiCallList
  typedef std::vector<ApiEntry> BBApiList;

  struct ApiCallInfo
  {

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

    ApiEntry& getFinalAnalysis()
    {
      return m_bblist.back();
    }

    // data flow information for each basic block in this function
    BBApiList m_bblist;

    // A pointer to the function itself
    const Function* m_func;

    std::vector<const Function*> m_path;
  };

  class ApiAnalysisPass : public ModulePass
  {
    // functions/instructions that call an API of interest
    std::set< std::pair<const Function*, std::string> > m_apicalllist;

    // The API name to look for
    std::vector<std::string> m_apilist;

    // these are functions without any callers, they are potential entry points
    // for the pattern
    std::vector<const Function*> m_startingPoints;

    // Dataflow analysis for each function
    std::vector<ApiCallInfo> m_apiAnalysis;

    void parseApiString(std::string apistring);

    void findStartingPoints(const Function* F);

    void analyze(const Function *F, unsigned int& progress, ApiCallInfo& aci);

    void defineEntryFunction(Module &M); 

    void printModule(Module &M);
    
    void printFunction(Function *F);

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

    virtual StringRef getPassName () const
    { return "ApiAnalysisPass"; }
  };
}
#endif /* _CALL_API_PASS_HH_ */
