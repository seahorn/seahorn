#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/Transforms/Scalar/PromoteVerifierCalls.hh"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"
namespace seahorn
{
  using namespace llvm;

  char CanFail::ID = 0;

  bool CanFail::canFail (const Function *f) const
  {return m_must.count (f) > 0 || m_may.count (f) > 0;}

  bool CanFail::runOnModule (Module &M)
  {
    LOG ("canfail", errs () << "Running mark-fail analysis\n";);

    if (const Function *errorFn = M.getFunction ("verifier.error"))
      m_must.insert (errorFn);

    LOG ("canfail", errs () << "Number of must_fail: " << m_must.size () << "\n";);


    // -- no error function found at all
    if (m_must.empty ()) return false;

    CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
    for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
    {
      auto &scc = *it;
      bool mark = false;

      // -- check if any of the functions in the scc calls something
      // -- that may fail
      for (CallGraphNode *cgn : scc)
      {
        for (auto &calls : *cgn)
          if (canFail (calls.second->getFunction ()))
          {mark=true; break;}
      }
      if (mark)
      {
        for (auto *cgn : scc)
          if (cgn->getFunction ())
            m_may.insert (cgn->getFunction ());
      }
    }

    LOG ("canfail", errs () << "Can fail: ";
         for (auto v : m_may) errs () << v->getName () << ", ";
         errs () << "\n";);


    return false;
  }

  void CanFail::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<PromoteVerifierCalls> ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  }

    Pass* createCanFailPass(){return new CanFail();}
}



static llvm::RegisterPass<seahorn::CanFail>
X ("mark-fail", "Mark functions that can fail");
