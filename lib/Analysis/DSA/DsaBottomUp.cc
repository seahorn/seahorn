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
#include "llvm/Support/raw_ostream.h"

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
      if (calleeG.hasRetCell (callee))
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
        if (calleeG.hasCell (*fml))
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

      LOG("dsa-bu", errs () << "Started bottom-up analysis ... \n");

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

          // -- visit all callsites in the callgraph node
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

            SimulationMapperRef sm (new SimulationMapper());
            bool res = Graph::computeCalleeCallerMapping(dsaCS, calleeG, callerG, 
                                                         true  /*only modified nodes*/, 
                                                         true, /*report if sanity check failed*/
                                                         *sm);
            if (!res) errs () << "WARNING " 
                              << *(dsaCS.getInstruction())  << ": "
                              << "caller does not simulate callee\n";
            assert (res);
            m_callee_caller_map.insert(std::make_pair(dsaCS.getInstruction(), sm));

          }
        }

        if (fGraph) fGraph->compress();        
      }

      LOG("dsa-bu", errs () << "Finished bottom-up analysis\n");
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
        if (F.isDeclaration() || F.empty())
          continue;

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
X ("sea-dsa-bu", "Bottom-up DSA pass");

