#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"

#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"

#include "llvm/Analysis/CallGraph.h"
//#include "llvm/Analysis/CallGraphSCCPass.h"

#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Local.hh"

#include "avy/AvyDebug.h"

using namespace llvm;

namespace seahorn
{
  namespace dsa
  {
      
    // wrapper to run a pass without relying on the global pass manager
    void runModulePass (Module &M, Pass *P) 
    {
      PassManager PM;
      PM.add (P);
      PM.run (M);
    }

    Global::Global () 
        : ModulePass (ID), 
          m_dl (nullptr), m_tli (nullptr), 
          m_graph (nullptr) {}
  
    void Global::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }
  
    bool Global::runOnModule (Module &M)
    {
      m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      m_tli = &getAnalysis<TargetLibraryInfo> ();

      // --- Compute the local graphs for each function
      Local *graphs = new Local ();
      runModulePass(M, graphs);

      LOG ("dsa-global",
           for (auto &F: M) {
             if (graphs->hasGraph (&F)) {
               auto const &g = graphs->getGraph(&F);
               g.write (errs());
             }
           });


      // -- the global graph
      m_graph.reset (new Graph(*m_dl));

      /* TODO:
         
         - bottom-up inline of all function graphs
         - resolve all calls by unifying formal and actual parameters
      */
      
      return false;
    }

    const Graph& Global::getGraph() const { return *m_graph; }
  
  } // end namespace dsa
} // end namespace seahorn

char seahorn::dsa::Global::ID = 0;
