#include "seahorn/Analysis/CallApiPass.hh"

/**
* Identifies functions that call a specific API function
*/
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"
#include "avy/AvyDebug.h"
#include "llvm/ADT/SCCIterator.h"

namespace seahorn
{
  using namespace llvm;

  void CallApiPass::sortTopo(const Function &F) {

    outs() << "SCCs for " << F.getName() << " in post-order:\n";

    for (scc_iterator<Function *> I = scc_begin(&F),
      IE = scc_end(&F);
      I != IE; ++I) {

        // Obtain the vector of BBs in this SCC and print it out.
        const std::vector<BasicBlock *> &SCCBBs = *I;
        outs() << "  SCC: ";
        for (std::vector<BasicBlock *>::const_iterator BBI = SCCBBs.begin(),
        BBIE = SCCBBs.end();
        BBI != BBIE; ++BBI) {
          outs() << (*BBI)->getName() << "  ";
      }
      outs() << "\n";
    }


    // std::vector<const BasicBlock*> outBlocks;
    //
    // RevTopoSort(F,outBlocks);
    //
    // outs() << ""
    //
    // for (const BasicBlock *bb : outBlocks)
    // {
    //   outs() << "BB: " << bb->getName() << "\n";
    // }

  }


  void CallApiPass::parseApiString(std::string apistring) {

    std::istringstream ss(apistring);
    std::string token;
    while(std::getline(ss, token, ',')) {
      m_apis.push_back(token);
    }
  }

  // The body of the pass
  bool CallApiPass::runOnModule (Module &M)
  {
    for (std::string API : m_apis)
    {
      for (Function &F : M)
      {

        sortTopo(F);

        for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i)
        {
          Instruction *I = &*i;
          if (const CallInst *CI = dyn_cast<CallInst> (I)) {
            CallSite CS (const_cast<CallInst*> (CI));
            const Function *cf = CS.getCalledFunction ();

            if (cf) {

              if (cf->getName().str() == API) {
                m_apicalllist.insert(std::make_pair(&F,API));
                m_progress++;
              }
            }
          }
        }
      }
    }

    // This is a check to determine if all of the required APIs have been found
    if (m_progress != m_apis.size()) {
      outs() << "Could not find all API functions.\n";
    }
    else
    {
      outs () << "Found calls to " << m_apicalllist.size() << " API functions:\n";
      for (auto v : m_apicalllist)
      {
        outs () << v.first->getName () << " calls " << v.second << "\n";
      }
    }

    return false;
  }

  void CallApiPass::getAnalysisUsage (AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  }

  char CallApiPass::ID = 0;

  llvm::Pass *createCallApiPass(std::string &config) {
    return new CallApiPass(config);
  }

  llvm::Pass *createCallApiPass() {
    return new CallApiPass();
  }
}   // namespace seahorn

static llvm::RegisterPass<seahorn::CallApiPass>
X("call-api", "Determine if a given API is called",false, false);
