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

    // Required API calls are initialized for this BB
    BBApiMap bbmap;
    for (const BasicBlock *bb : sortedBBlocks)
    {

      bbmap[bb] = apilist; // initially, everything is false (not found)

      for (std::string API : m_apilist)
      {
        for (BasicBlock::const_iterator bi = bb->begin(); bi != bb->end(); bi++)
        {
          const Instruction *I = &*bi;
          if (const CallInst *CI = dyn_cast<CallInst> (I)) {
            CallSite CS (const_cast<CallInst*> (CI));
            const Function *cf = CS.getCalledFunction();

            // this block contains an API function call of interest
            if (cf) {
              if (cf->getName().str() == API)
              {
                for (auto &entry : bbmap[bb])
                {
                  if (entry.first == API) entry.second = true;
                }
              }
            }
          }
        }
      }
    }
    // Save the bbmap for this function
    m_funcmap[&F] = bbmap;
  }

  void ApiAnalysisPass::propagateAnalysis()
  {
    // for each function
    for (auto& fentry : m_funcmap)
    {
      Function *curfunc = fentry.first;
      BBApiMap& bbmap = fentry.second;;

      ApiCallList prev;
      for (std::string API : m_apilist)
      {
        prev.push_back(std::make_pair(API,false));
      }


      if (!bbmap.empty())
      {
        for (auto& bbentry : bbmap)
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
    propagateAnalysis();

    for (auto &fentry : m_funcmap)
    {
      if (!fentry.second.empty())
      {
        outs () << fentry.first->getName() << "\n";
        for (auto bentry : fentry.second)
        {
          for (auto &aentry : bentry.second)
          {
            outs() << "\t" << aentry.first << ": " << aentry.second << "\n";
          }
        }
      }
      outs() << "\n";
    }

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
