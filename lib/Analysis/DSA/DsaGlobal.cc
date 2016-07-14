#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Local.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"

#include "avy/AvyDebug.h"

#include "boost/range/iterator_range.hpp"

using namespace llvm;

namespace seahorn
{
  namespace dsa
  {
      
    Global::Global () 
      : ModulePass (ID), m_dl (nullptr), m_tli (nullptr)  {}
          
    void Global::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }
    

    void Global::resolveCallSite (DsaCallSite &CS)
    {

      // unify globals 
      for (auto &kv : boost::make_iterator_range (m_graph->globals_begin (),
                                                  m_graph->globals_end ()))
      {
        Cell &nc = m_graph->mkCell (*kv.first, Cell ());
        nc.unify (*(kv.second));
      }

      // unify return
      const Function &callee = *CS.getCallee ();
      if (m_graph->hasCell(*CS.getInstruction()) && m_graph->hasRetCell(callee))
      {
        Cell &nc = m_graph->mkCell(*CS.getInstruction(), Cell());
        const Cell& r = m_graph->getRetCell(callee);
        Cell c (*r.getNode (), r.getOffset ());
        nc.unify(c);
      }

      // unify actuals and formals
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
      m_tli = &getAnalysis<TargetLibraryInfo> ();


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
      m_graph.reset (new Graph(*m_dl, m_setFactory));

      LocalAnalysis la (*m_dl, *m_tli);
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
          if (!F || F->isDeclaration () || F->empty ()) continue;
          
          // compute local graph
          Graph fGraph (*m_dl, m_setFactory);
          la.runOnFunction (*F, fGraph);

          LOG ("dsa-inlining",
               errs () << "\tImporting graph of " << F->getName() << "\n";);

          m_graph->import(fGraph, true);
        }
      }

      // -- resolve calls by unifying formal and actual parameters
      for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc)
        {
          Function *F = cgn->getFunction ();
          
          // XXX probably not needed since if the function is external
          // XXX it will have no call records
          if (!F || F->isDeclaration () || F->empty ()) continue;
          
          // -- iterate over all call instructions of the current function F
          // -- they are indexed in the CallGraphNode data structure
          for (auto &CallRecord : *cgn) 
          {

            ImmutableCallSite CS(CallRecord.first);
            DsaCallSite dsa_cs(CS);
            const Function *Callee = dsa_cs.getCallee();
            // XXX We want to resolve external calls as well.
            // XXX By not resolving them, we pretend that they have no
            // XXX side-effects. This should be an option, not the only behavior
            if (Callee && !Callee->isDeclaration () && !Callee->empty ())
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

