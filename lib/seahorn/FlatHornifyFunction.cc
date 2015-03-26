#include "seahorn/FlatHornifyFunction.hh"
#include "seahorn/LiveSymbols.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/ExprSeahorn.hh"

namespace seahorn
{
  /// Find a function exit basic block.  Assumes that the function has
  /// a unique block with return instruction
  static const BasicBlock* findExitBlock (const Function &F)
  {
    for (const BasicBlock& bb : F)
      if (isa<ReturnInst> (bb.getTerminator ())) return &bb;
    return NULL;
  }
  
  void FlatLargeHornifyFunction::runOnFunction (Function &F)
  {

    const BasicBlock *exit = findExitBlock (F);
    if (!exit)
    {
      errs () << "The exit block of " << F.getName () << " is unreachable.\n";
      return;
    }


    CutPointGraph &cpg = m_parent.getCpg (F);
    const LiveSymbols &ls = m_parent.getLiveSybols (F);
    
    ExprVector sorts;

    for (const CutPoint &cp : cpg)
    {
      Expr decl = m_parent.bbPredicate (cp.bb ());
      m_fp.registerRelation (decl);
      if (m_interproc) extractFunctionInfo (cp.bb ());
    }
          
    const BasicBlock &entry = F.getEntryBlock ();
    
    ExprSet allVars;
    ExprVector args;
    SymStore s (m_efac);
    for (const Expr& v : ls.live (&entry)) args.push_back (s.read (v));
    allVars.insert (args.begin (), args.end ());
    
    Expr rule = bind::fapp (m_parent.bbPredicate (entry), args);
    rule = boolop::limp (boolop::lneg (s.read (m_sem.errorFlag (entry))), rule);
    m_fp.addRule (allVars, rule);
    allVars.clear ();
    
    UfoLargeSymExec lsem (m_sem);
    
    for (const CutPoint &cp : cpg)
      {
        for (const CpEdge *edge : boost::make_iterator_range (cp.succ_begin (),
                                                              cp.succ_end ()))
        {
          allVars.clear ();
          args.clear ();
          s.reset ();
          const ExprVector &live = ls.live (&cp.bb ());

          for (const Expr &v : live) args.push_back (s.read (v));
          allVars.insert (args.begin (), args.end ());
          
          Expr pre = bind::fapp (m_parent.bbPredicate (cp.bb ()), args);
          
          ExprVector side;
          side.push_back (boolop::lneg ((s.read (m_sem.errorFlag (cp.bb ())))));
          lsem.execCpEdg (s, *edge, side);
          Expr tau = mknary<AND> (mk<TRUE> (m_efac), side);
          expr::filter (tau, bind::IsConst(), 
                        std::inserter (allVars, allVars.begin ()));

          const BasicBlock &dst = edge->target ().bb ();
          args.clear ();
          for (const Expr &v : ls.live (&dst)) args.push_back (s.read (v));
          allVars.insert (args.begin (), args.end ());
          
          Expr post = bind::fapp (m_parent.bbPredicate (dst), args);
          m_fp.addRule (allVars, boolop::limp (boolop::land (pre, tau), post));
        }
      }
    
    allVars.clear ();
    args.clear ();
    s.reset ();
    
    // Add error flag exit rules
    // bb (err, V) & err -> bb_exit (err , V)
    assert(exit);

    for (const CutPoint &cp : cpg)
    {
      if (&cp.bb () == exit) continue;
      
      // XXX Can optimize. Only need the rules for BBs that trip the
      // error flag (directly or indirectly)
      s.reset ();
      allVars.clear ();
      args.clear ();
      
      const ExprVector &live = ls.live (&cp.bb ());
      for (const Expr &v : live) args.push_back (s.read (v));
      allVars.insert (args.begin (), args.end ());
      
      Expr pre = bind::fapp (m_parent.bbPredicate (cp.bb ()), args);
      pre = boolop::land (pre, s.read (m_sem.errorFlag (cp.bb ())));
      
      args.clear ();
      for (const Expr &v : ls.live (exit)) args.push_back (s.read (v));
      allVars.insert (args.begin (), args.end ());
      
      Expr post = bind::fapp (m_parent.bbPredicate (*exit), args);
      m_fp.addRule (allVars, boolop::limp (pre, post));
    }   
    
    if (F.getName ().equals ("main") && ls.live (exit).size () == 1)
      m_fp.addQuery (bind::fapp (m_parent.bbPredicate(*exit), mk<TRUE> (m_efac)));
    else if (F.getName ().equals ("main") && ls.live (exit).size () == 0)
      m_fp.addQuery (bind::fapp (m_parent.bbPredicate(*exit)));
    else if (m_interproc)
    {
      // the summary rule
      // exit(live_at_exit) & !error.flag ->
      //     summary(true, false, false, regions, arguments, globals, return)
      
      args.clear ();
      allVars.clear ();
      
      const ExprVector &live = ls.live (exit);
      for (const Expr &v : live) args.push_back (s.read (v)); 
      allVars.insert (args.begin (), args.end ());
      
      Expr pre = bind::fapp (m_parent.bbPredicate (*exit), args);
      pre = boolop::land (pre, boolop::lneg (s.read (m_sem.errorFlag (*exit))));
      
      Expr falseE = mk<FALSE> (m_efac);
      ExprVector postArgs {mk<TRUE> (m_efac), falseE, falseE};
      const FunctionInfo &fi = m_sem.getFunctionInfo (F);
      fi.evalArgs (m_sem, s, std::back_inserter (postArgs));
      std::copy_if (postArgs.begin () + 3, postArgs.end (), 
                    std::inserter (allVars, allVars.begin ()),
                    bind::IsConst());
      Expr post = bind::fapp (fi.sumPred, postArgs);
      m_fp.addRule (allVars, boolop::limp (pre, post));
      
      // the error rule
      // bb_exit (true, V) -> S(true, false, true, V)
      pre = boolop::land (pre->arg (0), s.read (m_sem.errorFlag (*exit)));
      postArgs [2] = mk<TRUE> (m_efac);
      post = bind::fapp (fi.sumPred, postArgs);
      m_fp.addRule (allVars, boolop::limp (pre, post));
    }
    else if (!exit & m_interproc) assert (0);
  }
}
