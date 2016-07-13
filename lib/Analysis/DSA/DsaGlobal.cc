#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Local.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"

#include "avy/AvyDebug.h"

using namespace llvm;

namespace seahorn
{
  namespace dsa
  {
      
    Global::Global () 
        : ModulePass (ID), m_dl (nullptr), m_graph (nullptr) {}
          
    void Global::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<seahorn::dsa::Local> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }
    

    void Global::resolveCallSite (DsaCallSite &CS)
    {
      // Handle the return value of the function...
      const Function &F = *CS.getCallee ();
      const Value* retVal = CS.getRetVal();
      if ((retVal && m_graph->hasCell(*retVal)) && m_graph->hasRetCell(F))
      {
        Cell &c  = m_graph->mkCell(*retVal, Cell());
        c.unify(m_graph->mkRetCell(F, Cell()));
      }

      // Loop over all actual arguments, unifying them with the formal
      // ones
      DsaCallSite::const_actual_iterator AI = CS.actual_begin(), AE = CS.actual_end();
      for (DsaCallSite::const_formal_iterator FI = CS.formal_begin(), FE = CS.formal_end();
           FI != FE && AI != AE; ++FI, ++AI) 
      {
        const Value *arg = (*AI).get();
        const Value *farg = &*FI;
        if (m_graph->hasCell(*farg) && m_graph->hasCell(*arg)) {
          Cell &c = m_graph->mkCell(*arg, Cell());
          Cell &d = m_graph->mkCell (*farg, Cell ());
          c.unify (d);
        }
      }

    }                                      
    
    bool Global::runOnModule (Module &M)
    {
      m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();

      // --- Get the local graphs for each function
      Local *graphs = &getAnalysis<seahorn::dsa::Local> ();

      // LOG ("dsa-global",
      //      errs () << "==============\n";
      //      errs () << "*** LOCAL ***\n";
      //      errs () << "==============\n";
      //      for (auto &F: M) {
      //        if (graphs->hasGraph (F)) {
      //          auto const &g = graphs->getGraph(F);
      //          g.write (errs());
      //        }
      //      });

      // -- the global graph
      m_graph.reset (new Graph(*m_dl));

      // -- bottom-up inline of all graphs
      CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
      for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;

        LOG ("dsa-inlining", errs () << "SCC\n";);

        for (CallGraphNode *cgn : scc) 
        {
          
          LOG ("dsa-inlining", errs () << "\t"; cgn->print (errs ()); errs () << "\n");

          Function *F = cgn->getFunction ();
          if (F && graphs->hasGraph(*F)) 
          {

            LOG ("dsa-inlining",
                 errs () << "\tImported graph from " << F->getName() <<"\n";);

            m_graph->import(graphs->getGraph(*F), true);
          }
        }
      }

      // -- resolve calls by unifying formal and actual parameters
      for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc)
        {
          Function *F = cgn->getFunction ();
          if (!F || !graphs->hasGraph(*F)) continue;
          
          // -- iterate over all call instructions of the current function F
          // -- they are indexed in the CallGraphNode data structure
          for (auto &CallRecord : *cgn) 
          {

            ImmutableCallSite CS(CallRecord.first);
            DsaCallSite dsa_cs(CS);
            const Function *Callee = dsa_cs.getCallee();
            if (Callee && graphs->hasGraph(*Callee)) 
            {
              LOG ("dsa-resolve",
                   errs () << "Resolving call site " << *(dsa_cs.getInstruction()) << "\n");
              
              assert (F == dsa_cs.getCaller ());
              resolveCallSite (dsa_cs);
            }

          }
        }
        m_graph->compress();
      }
      m_graph->compress();

      LOG ("dsa-global",
           errs () << "==============\n";
           errs () << "*** GLOBAL ***\n";
           errs () << "==============\n";
           m_graph->write (errs ()));
      
      return false;
    }

    Graph& Global::getGraph() { return *m_graph; }

    const Graph& Global::getGraph() const { return *m_graph; }
  
  } // end namespace dsa
} // end namespace seahorn

char seahorn::dsa::Global::ID = 0;

static llvm::RegisterPass<seahorn::dsa::Global> 
X ("dsa-global", "Context-insensitive Dsa analysis");

