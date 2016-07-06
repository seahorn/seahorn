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

namespace seahorn
{
  namespace dsa
  {
      
    Global::Global () 
        : ModulePass (ID), m_dl (nullptr), m_graph (nullptr) {}
          
    void Global::getAnalysisUsage (AnalysisUsage &AU) const 
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.setPreservesAll ();
    }

    Value* getRetVal (const CallSite &CS) {
      if (CallInst* CI = dyn_cast<CallInst>(CS.getInstruction())) {
        if (!CI->getType()->isVoidTy ())
          return CI;
      }
      return nullptr;
    }

    void Global::resolveFunctionCall (const Function *F, const CallSite &CS)
    {
      // Handle the return value of the function...
      Value* retVal = getRetVal(CS);
      if ((retVal && m_graph->hasCell(*retVal)) && m_graph->hasRetCell(*F)) {
        Cell &c  = m_graph->mkCell(*retVal, Cell());
        c.unify(m_graph->mkRetCell(*F, Cell()));
      }

      // Loop over all arguments, unifying them with the formal ones
      unsigned argIdx = 0;
      for (Function::const_arg_iterator AI = F->arg_begin(), AE = F->arg_end();
           AI != AE && argIdx < CS.arg_size(); ++AI, ++argIdx) 
      {
        const Value *arg = &*AI;
        if (m_graph->hasCell(*arg) && m_graph->hasCell(*(CS.getArgument(argIdx)))) {
          Cell &c = m_graph->mkCell(*(CS.getArgument(argIdx)), Cell());
          c.unify(m_graph->mkCell (*arg, Cell()));
        }
      }
    }                                      
    
    bool Global::runOnModule (Module &M)
    {
      m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();

      // --- Get the local graphs for each function
      Local *graphs = new Local ();
      PassManager PM;
      PM.add (graphs);
      PM.run (M);

      LOG ("dsa-global",
           errs () << "==============\n";
           errs () << "*** LOCAL ***\n";
           errs () << "==============\n";
           for (auto &F: M) {
             if (graphs->hasGraph (F)) {
               auto const &g = graphs->getGraph(F);
               g.write (errs());
             }
           });

      // -- the global graph
      m_graph.reset (new Graph(*m_dl));

      // -- bottom-up inline of all graphs
      CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
      for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc)
          for (auto &calls : *cgn) 
          {
            Function *F = calls.second->getFunction ();
            if (F && graphs->hasGraph(*F))
              m_graph->import(graphs->getGraph(*F), true);
          }
      }

      // -- resolve calls by unifying formal and actual parameters
      for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc)
          for (auto &calls : *cgn) 
          {
            Function *F = calls.second->getFunction ();
            if (!F || !graphs->hasGraph(*F)) continue;

            for (inst_iterator i = inst_begin(*F), e = inst_end(*F); i != e; ++i) 
            {
              Instruction *I = &*i;
              if (CallInst * CI = dyn_cast<CallInst>(I)) {
                CallSite CS (CI);
                resolveFunctionCall (F, CS);
              }
            }
          }
      }

      LOG ("dsa-global",
           errs () << "==============\n";
           errs () << "*** GLOBAL ***\n";
           errs () << "==============\n";
           m_graph->write (errs ()));
      
      return false;
    }

    const Graph& Global::getGraph() const { return *m_graph; }
  
  } // end namespace dsa
} // end namespace seahorn

char seahorn::dsa::Global::ID = 0;
