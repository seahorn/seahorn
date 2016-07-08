#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Pass.h"
#include "llvm/PassManager.h"

#include "llvm/IR/DataLayout.h"

#include "llvm/Analysis/CallGraph.h"

#include "llvm/ADT/SCCIterator.h"

#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Local.hh"

#include "avy/AvyDebug.h"

using namespace llvm;

static Value* getRetVal (const CallSite &CS)
{
  if (Function *F = CS.getCalledFunction ())
  {
    FunctionType *FTy = F->getFunctionType ();
    if (!(FTy->getReturnType()->isVoidTy ()))
      return CS.getInstruction ();
  }
  return nullptr;
}


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
    

    void Global::resolveCallSite (const CallSite &CS)
    {
      // Handle the return value of the function...
      Function &F = *CS.getCalledFunction ();
      Value* retVal = getRetVal(CS);
      if ((retVal && m_graph->hasCell(*retVal)) && m_graph->hasRetCell(F))
      {
        Cell &c  = m_graph->mkCell(*retVal, Cell());
        c.unify(m_graph->mkRetCell(F, Cell()));
      }

      // Loop over all arguments, unifying them with the formal ones
      unsigned argIdx = 0;
      for (Function::const_arg_iterator AI = F.arg_begin(), AE = F.arg_end();
           AI != AE && argIdx < CS.arg_size(); ++AI, ++argIdx) 
      {
        const Value *arg = &*AI;
        if (m_graph->hasCell(*arg) &&
            m_graph->hasCell(*(CS.getArgument(argIdx)))) {
          Cell &c = m_graph->mkCell(*(CS.getArgument(argIdx)), Cell());
          Cell &d = m_graph->mkCell (*arg, Cell ());
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

            CallSite CS (CallRecord.first);
            Function *Callee = CS.getCalledFunction();
            if (Callee && graphs->hasGraph(*Callee)) 
            {
              LOG ("dsa-resolve",
                   errs () << "Resolving call site " << *(CS.getInstruction()) << "\n");
              
              assert (F == CS.getCaller ());
              resolveCallSite (CS);
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

