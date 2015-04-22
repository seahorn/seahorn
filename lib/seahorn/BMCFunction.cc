#include "seahorn/BMCFunction.hh"
#include "seahorn/LiveSymbols.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/ExprSeahorn.hh"

namespace seabmc
{

  /// Find a function exit basic block.  Assumes that the function has
  /// a unique block with return instruction
  static const BasicBlock* findExitBlock (const Function &F)
  {
    for (const BasicBlock& bb : F)
      if (isa<ReturnInst> (bb.getTerminator ())) return &bb;
    return NULL;
  }


   void SmallBMCFunction::runOnFunction (Function &F)
  {
    errs() << "Still to be implemented";
    return;
  }

  void LargeBMCFunction::runOnFunction (Function &F)
  {
    CutPointGraph &cpg = m_parent.getCpg (F);
    const LiveSymbols &ls = m_parent.getLiveSybols (F);

    ExprVector sorts;
    // -- SMT solver for BMC
    ZSolver<EZ3> bmc_smt (m_zctx);

    for (const CutPoint &cp : cpg)
    {
      Expr decl = m_parent.bbPredicate (cp.bb ());

    }

    const BasicBlock &entry = F.getEntryBlock ();

    ExprSet allVars;
    ExprVector args;
    SymStore s (m_efac);
    for (const Expr& v : ls.live (&entry)) args.push_back (s.read (v));
    allVars.insert (args.begin (), args.end ());

    Expr entry_rule = bind::fapp (m_parent.bbPredicate (entry), args);
    entry_rule = boolop::limp (boolop::lneg (s.read (m_sem.errorFlag (entry))), entry_rule);
    LOG("bmc", errs() << "Entry Rule -> " << m_zctx.toSmtLib(entry_rule) << "\n");
    bmc_smt.assertExpr(entry_rule);
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
          Expr f = boolop::limp (boolop::land (pre, tau), post);
          bmc_smt.assertExpr(f);
          LOG("bmc", errs() << "Other rules -> " << m_zctx.toSmtLib(f) << "\n");
        }
      }

    allVars.clear ();
    args.clear ();
    s.reset ();

    boost::tribool res = bmc_smt.solve ();
    if (res) outs () << "sat";
    else if (!res) outs () << "unsat";
    else outs () << "unknown";
    outs () << "\n";

  }

}
