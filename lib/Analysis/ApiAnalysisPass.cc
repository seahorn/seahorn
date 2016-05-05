#include "seahorn/Analysis/ApiAnalysisPass.hh"

/**
* Identifies functions that call a specific API function
*/
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"
#include "avy/AvyDebug.h"
#include "llvm/ADT/SCCIterator.h"
#include "boost/range/algorithm/reverse.hpp"

namespace seahorn
{
  using namespace llvm;

  void ApiAnalysisPass::initialize(Function &F)
  {
    // First, get the basic blocks in topological order
    std::vector<const BasicBlock*> sortedBBlocks;
    RevTopoSort(F,sortedBBlocks);
    boost::reverse(sortedBBlocks);

    // initialize the API list with no APIs found for this BB
    ApiCallList apilist;
    for (std::string API : m_apilist)
    {
      apilist.push_back(std::make_pair(API,false));
    }

    ApiCallInfo aci;

    // Required API calls are initialized for this BB
    BBApiList bblist;
    for (const BasicBlock *bb : sortedBBlocks)
    {
      BBApiEntry bbentry = std::make_pair(bb, apilist);

      for (std::string API : m_apilist)
      {
        for (BasicBlock::const_iterator bi = bb->begin(); bi != bb->end(); bi++)
        {
          const Instruction *I = &*bi;
          if (const CallInst *CI = dyn_cast<CallInst> (I)) {

            CallSite CS (const_cast<CallInst*> (CI));
            const Function *cf = CS.getCalledFunction();

            // this block contains an API function call of interest
            if (cf)
            {
              if (cf->getName().str() == API)
              {
                for (auto &api : bbentry.second)
                {
                  // this should be ok, because we are comparing pointers
                  if (api.first == API)
                  {
                    api.second = true;
                    break;
                  }
                }
              }
            }
          }
        }
      }
      // save the BB list
      bblist.push_back(bbentry);
    }

    // save the analysis for this function
    aci.m_func = &F;
    aci.m_bblist = bblist;
    m_apiAnalysis.push_back(aci);
  }

  void ApiAnalysisPass::runFunctionAnalysis()
  {

    for (auto& analysis : m_apiAnalysis)
    {
      Function *curfunc = analysis.m_func;

      BBApiList& bblist = analysis.m_bblist;

      ApiCallList prev;
      for (std::string API : m_apilist)
      {
        prev.push_back(std::make_pair(API,false));
      }

      for (auto& bbentry : bblist)
      {
        const BasicBlock *bb = bbentry.first;

        ApiCallList& apilist = bbentry.second;

        for (size_t i=0; i<apilist.size(); i++)
        {
          ApiEntry& api = apilist[i];
          if (prev[i].first == api.first && prev[i].second != api.second)
          {
            apilist[i].second = true;
          }
          prev[i].first = api.first;
          prev[i].second = api.second;
        }
      }
    }
  }

  void ApiAnalysisPass::propagateFunctionAnalysis()
  {
    // at this point we need to sort the functions in bottom up order
    // and check interprocedural calls

  }

  void ApiAnalysisPass::report()
  {
    for (auto& analysis : m_apiAnalysis)
    {
      if (!analysis.m_bblist.empty())
      {
        outs () << analysis.m_func->getName() << "\n";
        for (auto bentry : analysis.m_bblist)
        {
          //bentry.first->dump();
          for (auto &aentry : bentry.second)
          {
            outs() << "\t" << aentry.first << ": " << aentry.second << "\n";
          }
          outs() << "\t---\n";
        }

          BBApiEntry final = analysis.getFinalAnalysis();
          for (auto &e : final.second)
          {
            outs() << "\t" << e.first << ": " << e.second << ",";
          }
          outs() << "\t\n---\n";

          outs() << "\n";
      }
    }
  }

  void ApiAnalysisPass::parseApiString(std::string apistring)
  {
    std::istringstream ss(apistring);
    std::string api;
    while(std::getline(ss, api, ','))
    {
      m_apilist.push_back(api);
    }
  }

  // The body of the pass
  bool ApiAnalysisPass::runOnModule (Module &M)
  {
    for (Function &F : M)
    {
      initialize(F);
    }

    runFunctionAnalysis();

    propagateFunctionAnalysis();

    report();

    return false;
  }

  void ApiAnalysisPass::getAnalysisUsage (AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  }

  char ApiAnalysisPass::ID = 0;

  llvm::Pass *createApiAnalysisPass(std::string &config) {
    return new ApiAnalysisPass(config);
  }

  llvm::Pass *createApiAnalysisPass() {
    return new ApiAnalysisPass();
  }
}   // namespace seahorn

static llvm::RegisterPass<seahorn::ApiAnalysisPass>
X("call-api", "Determine if a given API is called",false, false);
