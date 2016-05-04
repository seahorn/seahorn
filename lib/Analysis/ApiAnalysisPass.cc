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

  //
  // void ApiAnalysisPass::analyzeBBlock(const BasicBlock *bb)
  // {
  //
  //   for (std::string API : m_apilist)
  //   {
  //     for (BasicBlock::const_iterator bi = bb->begin(); bi != bb->end(); bi++)
  //     {
  //       {
  //         const Instruction *I = &*bi;
  //         if (const CallInst *CI = dyn_cast<CallInst> (I)) {
  //           CallSite CS (const_cast<CallInst*> (CI));
  //           const Function *cf = CS.getCalledFunction();
  //
  //           // this block contains an API function call of interest
  //           if (cf) {
  //             if (cf->getName().str() == API) {
  //               // add the bb
  //               outs() << "Found call to API: " << API << "\n";
  //             }
  //           }
  //         }
  //       }
  //     }
  //   }
  // }

  void ApiAnalysisPass::analyzeApisInFunction( Function &F)
  {

    std::vector<const BasicBlock*> sortedBBlocks;
    RevTopoSort(F,sortedBBlocks);
    boost::reverse(sortedBBlocks);

    // basic blocks now in topological order

    // initialize the API
    ApiCallList apilist;
    for (std::string API : m_apilist)
    {
      apilist.push_back(std::make_pair(API,false));
    }

    // Required API calls are initialized for this BB

    for (const BasicBlock *bb : sortedBBlocks)
    {
      for (std::string API : m_apilist)
      {
        for (BasicBlock::const_iterator bi = bb->begin(); bi != bb->end(); bi++)
        {
          {
            const Instruction *I = &*bi;
            if (const CallInst *CI = dyn_cast<CallInst> (I)) {
              CallSite CS (const_cast<CallInst*> (CI));
              const Function *cf = CS.getCalledFunction();

              // this block contains an API function call of interest
              if (cf) {
                if (cf->getName().str() == API)
                {
                  for (auto &entry : apilist)
                  {
                    if (entry.first == API) entry.second = true;
                  }

                  m_bbmap[bb] = apilist;
                }
              }
            }
          }
        }
      }
    }

    // outs() << "Function "
    // << F.getName() << " has " << sortedBBlocks.size() << " blocks\n";
    //
    // for (const BasicBlock *bb : sortedBBlocks)
    // {
    //   outs() << "BB: \n";
    //   bb->dump();
    // }
    // outs() << "----------------------------------\n";

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
      analyzeApisInFunction(F);
    }
    outs () << "Found calls to " << m_apicalllist.size() << " API functions:\n";
    for (auto entry : m_bbmap)
    {
      entry.first->dump();
      for (auto apilist : entry.second)
      {
        outs () << apilist.first << " : " << apilist.second  << "\n";
      }
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
