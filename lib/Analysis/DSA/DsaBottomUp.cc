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
    BottomUp::BottomUp () 
      : ModulePass (ID), m_dl (nullptr), m_tli (nullptr)  {}
          
    void BottomUp::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }
    

    void BottomUp::resolveCallSite (DsaCallSite &CS)
    {
      assert (m_graphs.count (CS.getCaller ()) > 0);
      assert (m_graphs.count (CS.getCallee ()) > 0);
      
      const Function &caller = *CS.getCaller ();
      const Function &callee = *CS.getCallee ();
      Graph &callerG = *(m_graphs.find (&caller)->second);
      Graph &calleeG = *(m_graphs.find (&callee)->second);
      
      Cloner C (callerG);
      
      // import and unify globals 
      for (auto &kv : boost::make_iterator_range (calleeG.globals_begin (),
                                                  calleeG.globals_end ()))
      {
        Node &n = C.clone (*kv.second->getNode ());
        Cell c (n, kv.second->getOffset ());
        Cell &nc = callerG.mkCell (*kv.first, Cell ());
        nc.unify (c);
      }

      // import and unify return
      if (calleeG.hasRetCell (callee) && callerG.hasCell (*CS.getInstruction ()))
      {
        Node &n = C.clone (*calleeG.getRetCell (callee).getNode ());
        Cell c (n, calleeG.getRetCell (callee).getOffset ());
        Cell &nc = callerG.mkCell (*CS.getInstruction (), Cell());
        nc.unify (c);
      }

      // import and unify actuals and formals
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

    bool BottomUp::runOnModule (Module &M)
    {
      m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      m_tli = &getAnalysis<TargetLibraryInfo> ();

      LocalAnalysis la (*m_dl, *m_tli);

      CallGraph &cg = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
      for (auto it = scc_begin (&cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        GraphRef fGraph = std::make_shared<Graph> (*m_dl, m_setFactory);
        
        // -- compute a local graph shared between all functions in the scc
        for (CallGraphNode *cgn : scc)
        {
          Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          la.runOnFunction (*fn, *fGraph);
          m_graphs[fn] = fGraph;
        }

        fGraph->compress ();
      }

      // -- resolve all function calls in the graph
      for (auto it = scc_begin (&cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
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
            
            resolveCallSite (dsaCS);
          }
        }
      }
      return false;
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

