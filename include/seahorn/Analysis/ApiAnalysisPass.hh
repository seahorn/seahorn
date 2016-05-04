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

#include "seahorn/Support/SortTopo.hh"
#include "llvm/ADT/PostOrderIterator.h"

namespace seahorn
{

  using namespace llvm;

  typedef std::pair<std::string, bool> ApiEntry;

  // This is a list of expected API entries
  typedef std::vector<ApiEntry> ApiCallList;

  // Each Basic block in a function will have an ApiCallList
  typedef DenseMap<const BasicBlock*, ApiCallList> BBApiMap;

  // Each Function will have an ApiCallList
  typedef DenseMap<Function*, BBApiMap> FuncApiMap;

  typedef std::pair<Function*, ApiCallList> FuncApiEntry;

  class ApiAnalysisPass : public ModulePass
  {
    // functions/instructions that call an API of interest
    std::set< std::pair<const Function*, std::string> > m_apicalllist;

    // The API name to look for
    std::vector<std::string> m_apilist;

    // Map of bb function calls to basic blocks
    FuncApiMap m_funcmap;

    FuncApiEntry m_funcApiEntry;

    ApiCallList initializeApiCallList();

    void parseApiString(std::string apistring);

    void initialize(Function &F);

    void propagateAnalysis();

    void analyzeBBlock(const BasicBlock* bb);

  public:

    static char ID;

    ApiAnalysisPass () : ModulePass (ID) { }

    ApiAnalysisPass (std::string &apistring) : ModulePass (ID) {
      parseApiString(apistring);
    }

    virtual bool runOnModule (Module &M);

    virtual void getAnalysisUsage (AnalysisUsage &AU) const;

    virtual const char* getPassName () const { return "ApiAnalysisPass"; }
  };
}
#endif /* _CALL_API_PASS_HH_ */
