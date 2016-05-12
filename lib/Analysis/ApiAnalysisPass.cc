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

  ApiCallInfo* ApiAnalysisPass::analyzeFunction(Function& F, ApiCallInfo *init_state)
  {
    for (auto analyzedfunc : m_apiAnalysis)
    {
      for (auto af : analyzedfunc.m_funcs)
      {
        if (af->getName() == F.getName())
        {
          bool done = analyzedfunc.m_progress == m_apilist.size();
          //outs() << "Already analyzed " << F.getName() << " and progress is " << done << "\n";
          if (done) return init_state;;
        }
      }
    }

    //outs() << "Analyzing " << F.getName() <<"\n";

    // First, get the basic blocks in topological order
    std::vector<const BasicBlock*> sortedBBlocks;
    RevTopoSort(F,sortedBBlocks);
    boost::reverse(sortedBBlocks);

    // initialize the API list with no APIs found for this BB
    ApiCallList apilist;
    for (std::string API : m_apilist)
    {
      apilist.push_back(std::make_pair(API, false));
    }

    ApiCallInfo *aci=NULL;
    if (init_state != NULL)
    {
      aci = init_state;
      //outs() << "Using existing state\n";
    }
    else
    {
      aci = new ApiCallInfo();
    }

    aci->m_funcs.push_back(&F);

    // Required API calls are initialized for this BB
    BBApiList bblist;
    std::string targetapi = m_apilist[aci->m_progress];

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
            // This is a call to the API of interest
            if (cf->getName().str() == targetapi)
            {
              // Found a call to the target, now record that and increment
              // progress
              for (unsigned int i = aci->m_progress; i<bbentry.second.size(); i++)
              {
                ApiEntry& apientry = bbentry.second[i];
                if (apientry.first == targetapi)
                {
                  outs() << "Found target API: " << targetapi << " in " << F.getName() << "\n";
                  apientry.second = true;

                  aci->m_finalapilist.push_back(std::make_pair(targetapi,true));

                  aci->m_funcs.push_back(cf);

                  if (0==aci->m_progress)
                  {
                    aci->m_startFunc = &F;
                  }
                  ++aci->m_progress;
                  break;
                }
              }
            }
            else
            {
              if (!cf->empty())
              {
                //outs() << "Calling Outgoing Function " << cf->getName() << "\n";
                aci = analyzeFunction(*cf,aci);

              }
            }
          }
        }
      } // for each insn

      // save the BB list
      bblist.push_back(bbentry);

      // are we done?
      if (aci->m_progress >= m_apilist.size())
      {
        outs() << "Complete sequence found!\n ";
        break;
      }

      // Pattern not found so move to to next API
      targetapi = m_apilist[aci->m_progress];
    }

    //outs() << "Saving results\n";

    // save the analysis for this function

    aci->m_bblist = bblist;

    return aci;
    //m_apiAnalysis.push_back(aci);
  }

  // void ApiAnalysisPass::propagateAnalysis(ApiCallInfo *analysis)
  // {
  //   // for each function, propagate the analysis
  //   for (auto& analysis : m_apiAnalysis)
  //   {
  //     Function *curfunc = analysis->m_func;
  //     BBApiList& bblist = analysis->m_bblist;
  //
  //     ApiCallList prev;
  //     for (std::string API : m_apilist)
  //     {
  //       prev.push_back(std::make_pair(API,false));
  //     }
  //
  //     for (auto& bbentry : bblist)
  //     {
  //       const BasicBlock *bb = bbentry.first;
  //       ApiCallList& apilist = bbentry.second;
  //
  //       for (size_t i=0; i<apilist.size(); i++)
  //       {
  //         ApiEntry& api = apilist[i];
  //
  //         if (prev[i].first == api.first && prev[i].second != api.second)
  //         {
  //           apilist[i].second = true;
  //         }
  //         prev[i].first = api.first;
  //         prev[i].second = api.second;
  //       }
  //     }
  //   }
  // }

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
        }
      }
    }
  }

  void ApiAnalysisPass::printFinalAnalysis() const
  {
    // for each function, propagate the analysis
    for (auto& analysis : m_apiAnalysis)
    {
      if (analysis.m_progress >= m_apilist.size())
      {
        outs() << "FINAL RESULTS:\n Required APIs called in required order starting at "
        << analysis.m_startFunc->getName() << "\nSequence of calls:\n";
        for (auto path : analysis.m_funcs)
        {
          outs() << "\t* " << path->getName() << "\n";
        }
      }
    }
  }

  void ApiAnalysisPass::reportResults()
  {
    // for (auto analysis : m_apiAnalysis)
    // {
    //   if (!analysis.m_bblist.empty())
    //   {
    //     if (analysis.m_func->getName() != "_ZN14CSystemManager14getProcessListEv") continue;
    //
    //     outs () << analysis.m_func->getName() << "\n";
    //
    //     for (auto bentry : analysis.m_bblist)
    //     {
    //       //bentry.first->dump();
    //       for (auto &aentry : bentry.second)
    //       {
    //         outs() << "\t" << aentry.first << ": " << aentry.second << "\n";
    //       }
    //       outs() << "\t---\n";
    //     }
    //
    //     printFinalAnalysis();
    //   }
    // }
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

    std::vector<Function*> sortedFuncs;
    // sort funcs in topo order
    CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph();
    for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
    {
      auto &scc = *it;
      for (CallGraphNode *cgn : scc)
      {
        Function *f = cgn->getFunction();
        if (!f) continue;
        sortedFuncs.push_back(f);
      }
    }

    // This call generates API call information for each
    for (Function *F : sortedFuncs)
    {
      m_apiAnalysis.push_back(analyzeFunction(*F,NULL));
    }

    printFinalAnalysis();

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
