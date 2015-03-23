#include "seahorn/HornSolver.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"
#include "ufo/Stats.hh"

#include "boost/range/algorithm/reverse.hpp"

using namespace llvm;

static llvm::cl::opt<bool>
PrintAnswer ("horn-answer",
             cl::desc ("Print Horn answer"), cl::init (false));

namespace seahorn
{
  char HornSolver::ID = 0;

  bool HornSolver::runOnModule (Module &M)
  {
    Stats::sset ("Result", "UNKNOWN");
    
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    // Load the Horn clause database
    auto &db = hm.getHornClauseDB ();
    // this will have effect only if -horn-clp-sem is enabled.
    normalizeHornClauseHeads (db);

    auto &fp = hm.getZFixedPoint ();
    db.loadZFixedPoint (fp);
    
    Stats::resume ("Horn");
    m_result = fp.query ();
    Stats::stop ("Horn");
    
    if (m_result) outs () << "sat"; 
    else if (!m_result) outs () << "unsat"; 
    else outs () << "unknown"; 
    outs () << "\n";

    if (m_result) Stats::sset ("Result", "FALSE");
    else if (!m_result) Stats::sset ("Result", "TRUE");
    
    LOG ("answer",
         if (m_result || !m_result) errs () << fp.getAnswer () << "\n";);


    if (PrintAnswer && !m_result)
      printInvars (M);
    else if (PrintAnswer && m_result)
      printCex ();
    
    return false;
  }

  void HornSolver::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll ();
  }

  void HornSolver::printCex ()
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    auto &fp = hm.getZFixedPoint ();
    //outs () << *fp.getCex () << "\n";
    
    ExprVector rules;
    fp.getCexRules (rules);
    boost::reverse (rules);
    for (Expr r : rules) 
    {
      Expr src;
      Expr dst;
      
      if (isOpX<IMPL> (r)) 
      { 
        dst = r->arg (1);
        r = r->arg (0);
        src = isOpX<AND> (r) ? r->arg (0) : r;
      }
      else
        dst = r;
      
      if (src)
      {
        if (!bind::isFapp (src)) src.reset (0);
        else src = bind::fname (bind::fname (src));
      }
      

      if (src) outs () << *src << " --> ";
      
      dst = bind::fname (bind::fname (dst));
      outs () << *dst << "\n";
    }
    
  }

  void HornSolver::printInvars (Module &M)
  {
    for (auto &F : M) printInvars (F);
  }

  void HornSolver::printInvars (Function &F)
  {
    if (F.isDeclaration ()) return;

    HornifyModule &hm = getAnalysis<HornifyModule> ();
    auto &fp = hm.getZFixedPoint ();

    outs () << "Function: " << F.getName () << "\n";

    // -- not used for now
    Expr summary = hm.summaryPredicate (F);

    for (auto &BB : F)
    {
      if (!hm.hasBbPredicate (BB)) continue;

      Expr bbPred = hm.bbPredicate (BB);

      outs () << *bind::fname (bbPred) << ":";
      const ExprVector &live = hm.live (BB);
      Expr invars = fp.getCoverDelta (bind::fapp (bbPred, live));

      if (isOpX<AND> (invars))
      {
        outs () << "\n\t";
        for (size_t i = 0; i < invars->arity (); ++i)
          outs () << "\t" << *invars->arg (i) << "\n";
      }
      else
        outs () << " " << *invars << "\n";
    }
  }

}
