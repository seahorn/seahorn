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

  void ApiAnalysisPass::analyzeFunction(Function &F)
  {
    outs() << "Analyzing " << F.getName() <<"\n";

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
    //unsigned int progress = 0;
    std::string targetapi = m_apilist[aci.m_progress];

    // for each of the sorted BBs,
    for (const BasicBlock *bb : sortedBBlocks)
    {
      //outs() << "Looking for " << targetapi << "\n";

      BBApiEntry bbentry = std::make_pair(bb, apilist);
      for (BasicBlock::const_iterator bi = bb->begin(); bi != bb->end(); bi++)
      {
        const Instruction *I = &*bi;
        if (const CallInst *CI = dyn_cast<CallInst> (I))
        {
          CallSite CS (const_cast<CallInst*> (CI));
          Function *cf = CS.getCalledFunction();

          // this block contains an API function call of interest
          if (cf)
          {
            //outs() << "\tFunction " << F.getName() << " calls " << cf->getName() << "\n";
            // This is a call to the API of interest
            if (cf->getName().str() == targetapi)
            {
              // Found a call to the target, now record that and increment
              // progress
              for (unsigned int i = aci.m_progress; i<bbentry.second.size(); i++)
              {
                ApiEntry& apientry = bbentry.second[i];
                if (apientry.first == targetapi)
                {
                  //outs() << "Found " << targetapi << "\n";
                  apientry.second = true;
                  ++aci.m_progress;
                  break;
                }
              }
            }
            else
            {
              if (!cf->empty())
              {
                outs() << "Saving called func "<< cf->getName() <<"\n";
                aci.m_outcalls.push_back(cf);
              }
            }
          }
        } // for each insn
        
        // save the BB list
        bblist.push_back(bbentry);

        // are we done?
        if (aci.m_progress >= m_apilist.size()) break;

        // move to next API
        targetapi = m_apilist[aci.m_progress];
      }
    }

    // save the analysis for this function
    aci.m_func = &F;
    aci.m_bblist = bblist;
    m_apiAnalysis.push_back(aci);
  }

  void ApiAnalysisPass::propagateAnalysis()
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

  void ApiAnalysisPass::runInterFunctionAnalysis()
  {
    // At this point we need to sort the functions in bottom up order
    // and check interprocedural calls
    //
    // We will need to rerun analysis from a given point

    CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph();
    for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
    {
      auto &scc = *it;
      for (CallGraphNode *cgn : scc)
      {
        Function *f = cgn->getFunction();
        if (!f) continue;
        outs() << f->getName() << " calls\n";
        for (auto& calls : *cgn)
        {
          Function *calledf = calls.second->getFunction();

          if (!calledf) continue;

          outs() << "\t" << calledf->getName() << "\n";

          // ApiCallInfo& currentfacts;
          // ApiCallInfo& calledfacts;
          // // have the function and the called function, now replace DF facts
          // for (auto& analysis : m_apiAnalysis)
          // {
          //   if (f->getName() == analysis.m_func->getName())
          //   {
          //     currentfacts = analysis;
          //   }
          //   if (calledf.getName() == analysis.m_func->getName())
          //   {
          //     calledfacts = analysis;
          //   }
          // }
        }
      }
    }
  }

  void ApiAnalysisPass::reportResults()
  {

    outs() << "FINAL RESULTS:\n";

    for (auto& analysis : m_apiAnalysis)
    {
      if (!analysis.m_bblist.empty())
      {
        // outs () << analysis.m_func->getName() << "\n";
        // for (auto bentry : analysis.m_bblist)
        // {
        //   //bentry.first->dump();
        //   for (auto &aentry : bentry.second)
        //   {
        //     outs() << "\t" << aentry.first << ": " << aentry.second << "\n";
        //   }
        //   outs() << "\t---\n";
        // }

        BBApiEntry final = analysis.getFinalAnalysis();
        bool result = true;
        for (auto &e : final.second)
        {
          if (!e.second)
          {
            result = false;
            break;
          }
        }

        if (result)
        {
          outs () << analysis.m_func->getName() << " calls required APIs in the required order\n";
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

    // This call generates API call information for each
    for (Function &F : M)
    {
      analyzeFunction(F);
    }
    propagateAnalysis();

    //propagateFunctionAnalysis();

    reportResults();

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
