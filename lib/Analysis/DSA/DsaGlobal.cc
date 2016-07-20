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

    void ContextInsensitiveGlobalAnalysis::
    resolveArguments (DsaCallSite &cs, Graph& g)
    {
      // unify return
      const Function &callee = *cs.getCallee ();
      if (g.hasCell(*cs.getInstruction()) && g.hasRetCell(callee))
      {
        Cell &nc = g.mkCell(*cs.getInstruction(), Cell());
        const Cell& r = g.getRetCell(callee);
        Cell c (*r.getNode (), r.getOffset ());
        nc.unify(c);
      }

      // unify actuals and formals
      DsaCallSite::const_actual_iterator AI = cs.actual_begin(), AE = cs.actual_end();
      for (DsaCallSite::const_formal_iterator FI = cs.formal_begin(), FE = cs.formal_end();
           FI != FE && AI != AE; ++FI, ++AI) 
      {
        const Value *arg = (*AI).get();
        const Value *farg = &*FI;
        if (g.hasCell(*farg) && g.hasCell(*arg)) {
          Cell &c = g.mkCell(*arg, Cell());
          Cell &d = g.mkCell (*farg, Cell ());
          c.unify (d);
        }
      }
    }                                      

    bool ContextInsensitiveGlobalAnalysis::
    runOnModule (Module &M, Graph& g, SetFactory &setFactory)
    {
      LocalAnalysis la (m_dl, m_tli);

      // -- bottom-up inline of all graphs
      for (auto it = scc_begin (&m_cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;

        // --- all scc members share the same local graph
        for (CallGraphNode *cgn : scc) 
        {
          Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          // compute local graph
          Graph fGraph (m_dl, setFactory);
          la.runOnFunction (*fn, fGraph);

          g.import(fGraph, true);
        }

        // --- resolve callsites
        for (CallGraphNode *cgn : scc)
        {
          Function *fn = cgn->getFunction ();
          
          // XXX probably not needed since if the function is external
          // XXX it will have no call records
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          // -- iterate over all call instructions of the current function fn
          // -- they are indexed in the CallGraphNode data structure
          for (auto &CallRecord : *cgn) 
          {
            ImmutableCallSite cs (CallRecord.first);
            DsaCallSite dsa_cs (cs);
            const Function *callee = dsa_cs.getCallee();
            // XXX We want to resolve external calls as well.
            // XXX By not resolving them, we pretend that they have no
            // XXX side-effects. This should be an option, not the only behavior
            if (callee && !callee->isDeclaration () && !callee->empty ())
            {
              assert (fn == dsa_cs.getCaller ());
              resolveArguments (dsa_cs, g);
            }
          }
        }
        g.compress();
      }

      LOG ("dsa-global",
           errs () << "==============\n*** GLOBAL ***\n==============\n";
           g.write (errs ()));
      
      return false;
    }

      
    ContextInsensitiveGlobal::ContextInsensitiveGlobal () 
      : ModulePass (ID) {}
          
    void ContextInsensitiveGlobal::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }
        
    bool ContextInsensitiveGlobal::runOnModule (Module &M)
    {
      auto dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      auto tli = &getAnalysis<TargetLibraryInfo> ();
      CallGraph &cg = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();

      m_graph.reset (new Graph(*dl, m_setFactory));

      ContextInsensitiveGlobalAnalysis  ga (*dl, *tli, cg);
      return ga.runOnModule (M, *m_graph, m_setFactory);
    }

    Graph& ContextInsensitiveGlobal::getGraph() 
    { assert(m_graph); return *m_graph; }

    const Graph& ContextInsensitiveGlobal::getGraph() const 
    { assert (m_graph); return *m_graph; }
  
  } // end namespace dsa
} // end namespace seahorn

char seahorn::dsa::ContextInsensitiveGlobal::ID = 0;

static llvm::RegisterPass<seahorn::dsa::ContextInsensitiveGlobal> 
X ("dsa-ci-global", "Context-insensitive Dsa analysis");

