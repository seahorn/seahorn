#include "seahorn/Analysis/DSA/CallGraph.hh"

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"

#include "avy/AvyDebug.h"

using namespace llvm;

namespace seahorn
{
  namespace dsa 
  {

    void DsaCallGraph::buildDependencies ()
    {
      // --- compute immediate predecessors (callsites) for each
      //     function in the call graph (considering only direct
      //     calls).
      // 
      // XXX: CallGraph cannot be reversed and the CallGraph analysis
      // doesn't seem to compute predecessors so I do not know a
      // better way.
      boost::unordered_map<const Function*, CallSiteSet> imm_preds;
      for (auto it = scc_begin (&m_cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;
        for (CallGraphNode *cgn : scc)
        {
          const Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          for (auto &callRecord : *cgn)
          { 
            ImmutableCallSite CS (callRecord.first);
            const Function *callee = CS.getCalledFunction ();
            if (!callee || callee->isDeclaration () || callee->empty ()) continue;

            auto predIt = imm_preds.find (callee);
            if (predIt != imm_preds.end ()) 
              insert (CS.getInstruction(), predIt->second); 
            else
            {
              CallSiteSet s;
              insert (CS.getInstruction (), s);
              imm_preds.insert (std::make_pair(callee, s));
            }
          }
        }
      }

      // -- compute uses/defs sets
      for (auto it = scc_begin (&m_cg); !it.isAtEnd (); ++it)
      {
        auto &scc = *it;

        // compute uses and defs shared between all functions in the scc 
        auto uses = std::make_shared<CallSiteSet>();
        auto defs = std::make_shared<CallSiteSet>();

        for (CallGraphNode *cgn : scc)
        {
          const Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;
          
          insert (imm_preds [fn].begin(), imm_preds [fn].end(), *uses);

          for (auto &callRecord : *cgn)
          {
            ImmutableCallSite CS (callRecord.first);
	    auto callee = CS.getCalledFunction ();
	    if (!callee || callee->isDeclaration () || callee->empty ())
	      continue;
            insert (CS.getInstruction(), *defs);
          }
        }

        // store uses and defs 
        for (CallGraphNode *cgn : scc)
        {
          const Function *fn = cgn->getFunction ();
          if (!fn || fn->isDeclaration () || fn->empty ()) continue;

          m_uses[fn] = uses;
          m_defs[fn] = defs;
        }
      }

      LOG ("dsa-cg",
	   errs () << "--- USES ---\n";
	   for (auto kv: m_uses) {
	     errs () << kv.first->getName () << " ---> \n";
	     for (auto &CS: *(kv.second)) {
	       errs () << "\t" << CS->getParent()->getParent()->getName () << ":" << *CS << "\n";
	     }
	   }
	   errs () << "--- DEFS ---\n";
	   for (auto kv: m_defs) {
	     errs () << kv.first->getName () << " ---> \n";
	     for (auto &CS: *(kv.second)) {
	       errs () << "\t" << *CS << "\n";
	     }
	   });
    }

  } // end namespace
} // end namespace 
