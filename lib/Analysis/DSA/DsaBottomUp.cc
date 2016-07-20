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
#include "seahorn/Analysis/DSA/BottomUp.hh"
#include "seahorn/Analysis/DSA/Local.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"
#include "seahorn/Analysis/DSA/Cloner.hh"

#include "avy/AvyDebug.h"

#include "boost/range/iterator_range.hpp"
using namespace llvm;

namespace seahorn
{
  namespace dsa
  {

    // Build a simulation mapping from calleeG to callerG
    bool BottomUpAnalysis::
    computeCalleeCallerMapping (const DsaCallSite &cs, 
                                Graph &calleeG, Graph &callerG, 
                                const bool onlyModified,
                                SimulationMapper &simMap) 
    {
      for (auto &kv : boost::make_iterator_range (calleeG.globals_begin (),
                                                  calleeG.globals_end ()))
      {
        Cell &c = *kv.second;
        if (!onlyModified || c.isModified ())
        {
          Cell &nc = callerG.mkCell (*kv.first, Cell ());
          if (!simMap.insert (c, nc)) return false; 
        }
      }

      const Function &callee = *cs.getCallee ();
      if (calleeG.hasRetCell (callee) && callerG.hasCell (*cs.getInstruction ()))
      {
        const Cell &c = calleeG.getRetCell (callee);
        if (!onlyModified || c.isModified()) 
        {
          Cell &nc = callerG.mkCell (*cs.getInstruction (), Cell());
          if (!simMap.insert (c, nc)) return false; 
        }
      }

      DsaCallSite::const_actual_iterator AI = cs.actual_begin(), AE = cs.actual_end();
      for (DsaCallSite::const_formal_iterator FI = cs.formal_begin(), FE = cs.formal_end();
           FI != FE && AI != AE; ++FI, ++AI) 
      {
        const Value *fml = &*FI;
        const Value *arg = (*AI).get();
        if (calleeG.hasCell (*fml) &&  callerG.hasCell (*arg)) {
          Cell &c = calleeG.mkCell (*fml, Cell ());
          if (!onlyModified || c.isModified ()) 
          {
            Cell &nc = callerG.mkCell (*arg, Cell ());
            if (!simMap.insert(c, nc)) return false; 
          }
        }
      }      
      return true;
    }

    // Clone callee nodes into caller and resolve arguments
    void BottomUpAnalysis::
    cloneAndResolveArguments (const DsaCallSite &CS, Graph& calleeG, Graph& callerG)
    {      
      Cloner C (callerG);
      
      // clone and unify globals 
      for (auto &kv : boost::make_iterator_range (calleeG.globals_begin (),
                                                  calleeG.globals_end ()))
      {
        Node &n = C.clone (*kv.second->getNode ());
        Cell c (n, kv.second->getOffset ());
        Cell &nc = callerG.mkCell (*kv.first, Cell ());
        nc.unify (c);
      }

      // clone and unify return
      const Function &callee = *CS.getCallee ();
      if (calleeG.hasRetCell (callee) && callerG.hasCell (*CS.getInstruction ()))
      {
        Node &n = C.clone (*calleeG.getRetCell (callee).getNode ());
        Cell c (n, calleeG.getRetCell (callee).getOffset ());
        Cell &nc = callerG.mkCell (*CS.getInstruction (), Cell());
        nc.unify (c);
      }

      // clone and unify actuals and formals
      DsaCallSite::const_actual_iterator AI = CS.actual_begin(), AE = CS.actual_end();
      for (DsaCallSite::const_formal_iterator FI = CS.formal_begin(), FE = CS.formal_end();
           FI != FE && AI != AE; ++FI, ++AI) 
      {
        const Value *arg = (*AI).get();
        const Value *fml = &*FI;
        if (callerG.hasCell (*arg) && calleeG.hasCell (*fml))
        {
          Node &n = C.clone (*calleeG.getCell (*fml).getNode ());
          Cell c (n, calleeG.getCell (*fml).getOffset ());
          Cell &nc = callerG.mkCell (*arg, Cell ());
          nc.unify (c);
        }
      }

      callerG.compress();
    }

    bool BottomUpAnalysis::runOnModule(Module &M, GraphMap &graphs) 
    {

      LocalAnalysis la (m_dl, m_tli);

      for (auto it = scc_begin (&m_cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;

        // -- compute a local graph shared between all functions in the scc
        GraphRef fGraph = nullptr;
        for (CallGraphNode *cgn : scc)
        {
          Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;

          if (!fGraph) {
            assert (graphs.find(fn) != graphs.end());
            fGraph = graphs[fn];
            assert (fGraph);
          }

          la.runOnFunction (*fn, *fGraph);
          graphs[fn] = fGraph;
        }

        // -- resolve all function calls in the graph
        for (CallGraphNode *cgn : scc)
        {
          Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          for (auto &callRecord : *cgn)
          {
            ImmutableCallSite CS (callRecord.first);
            DsaCallSite dsaCS (CS);
            const Function *callee = dsaCS.getCallee ();
            if (!callee || callee->isDeclaration () || callee->empty ()) continue;
            
            assert (graphs.count (dsaCS.getCaller ()) > 0);
            assert (graphs.count (dsaCS.getCallee ()) > 0);
      
            Graph &callerG = *(graphs.find (dsaCS.getCaller())->second);
            Graph &calleeG = *(graphs.find (dsaCS.getCallee())->second);
  
            cloneAndResolveArguments (dsaCS, calleeG, callerG);

            LOG ("dsa-bu", 
                 SimulationMapper simMap;
                 if (!computeCalleeCallerMapping(dsaCS, calleeG, callerG, true, simMap)) {
                   errs () << *(dsaCS.getInstruction())  << "\n"
                           << "  --- Caller does not simulate callee\n";
                 });
                 
          }
        }
        if (fGraph) fGraph->compress();        
      }
      
      return false;
    }

  
    BottomUp::BottomUp () 
      : ModulePass (ID), m_dl (nullptr), m_tli (nullptr)  {}
          
    void BottomUp::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }

    bool BottomUp::runOnModule (Module &M)
    {
      m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      m_tli = &getAnalysis<TargetLibraryInfo> ();
      CallGraph &cg = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();

      BottomUpAnalysis bu (*m_dl, *m_tli, cg);
      for (auto &F: M)
      { // XXX: the graphs must be created here
        GraphRef fGraph = std::make_shared<Graph> (*m_dl, m_setFactory);
        m_graphs[&F] = fGraph;
      }

      return bu.runOnModule (M, m_graphs);
    }

    Graph &BottomUp::getGraph (const Function &F) const
    { return *(m_graphs.find (&F)->second); }

    bool BottomUp::hasGraph (const Function &F) const
    { return m_graphs.count (&F) > 0; }

    char BottomUp::ID = 0;
  }
}

static llvm::RegisterPass<seahorn::dsa::BottomUp>
X ("dsa-bu", "Bottom-up DSA pass");

