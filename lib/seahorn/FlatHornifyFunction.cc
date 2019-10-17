#include "seahorn/FlatHornifyFunction.hh"
#include "seahorn/LiveSymbols.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/ExprSeahorn.hh"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn
{

  void FlatSmallHornifyFunction::runOnFunction (Function &F)
  {

    const BasicBlock *exit = findExitBlock (F);
    if (!exit)
    {
      errs () << "The exit block of " << F.getName () << " is unreachable.\n";
      return;
    }

    DenseMap<const BasicBlock*, Expr> pred;
    ExprVector sorts;

    const LiveSymbols &ls = m_parent.getLiveSybols (F);

    DenseMap<const BasicBlock*, unsigned long> bbOrder;
    // globally live
    ExprSet glive;
    unsigned idx = 0;

    for (auto &BB : F)
    {
      bbOrder [&BB] = idx++;
      auto &live = ls.live (&BB);
      glive.insert (live.begin (), live.end ());

      if (m_interproc) extractFunctionInfo (BB);
    }

    // -- process counter
    Expr pc = bind::intConst (mkTerm<std::string> ("flat.pc", m_efac));

    // -- step predicate. First argument is pc
    Expr step;
    {
      ExprVector sorts;
      sorts.reserve (glive.size () + 2);
      sorts.push_back (bind::typeOf (pc));
      for (auto &v : glive) sorts.push_back (bind::typeOf (v));
      sorts.push_back (mk<BOOL_TY> (m_efac));

      // the step function is
      Expr name = mkTerm<const Function*> (&F, m_efac);
      // avoid clash with the names of summaries
      if (m_interproc) name = variant::prime (name);

      step = bind::fdecl (name, sorts);
      m_db.registerRelation (step);
    }


    BasicBlock &entry = F.getEntryBlock ();

    ExprSet allVars;
    ExprVector args;
    SymStore s (m_efac);

    // create step(pc,x1,...,xn) for entry block
    s.write (pc, mkTerm<expr::mpz_class> (bbOrder [&entry], m_efac));
    args.push_back (s.read (pc));
    for (const Expr& v : glive) args.push_back (s.read (v));
    allVars.insert (++args.begin (), args.end ());

    Expr rule = bind::fapp (step, args);
    rule = boolop::limp (boolop::lneg (s.read (m_sem.errorFlag (entry))), rule);
    m_db.addRule (allVars, rule);

    for (auto &BB : F)
    {
      const BasicBlock *bb = &BB;
      for (const BasicBlock *dst : succs (*bb))
      {
        allVars.clear ();
        s.reset ();
        args.clear ();

    // create step(pc,x1,...,xn) for pre
        s.write (pc, mkTerm<expr::mpz_class> (bbOrder [bb], m_efac));
        args.push_back (s.read (pc));
        for (const Expr &v : glive) args.push_back (s.read (v));
        allVars.insert (++args.begin (), args.end ());
        assert(std::all_of(allVars.begin(), allVars.end(), bind::IsConst()));

        Expr pre = bind::fapp (step, args);

        // create tau
        ExprVector side;
        side.push_back (boolop::lneg ((s.read (m_sem.errorFlag (BB)))));
        m_sem.execEdg (s, BB, *dst, side);


        // create step(pc,x1,...,xn) for post
        args.clear ();
        s.write (pc, mkTerm<expr::mpz_class> (bbOrder [dst], m_efac));
        args.push_back (s.read (pc));
        for (const Expr &v : glive) {
          Expr argV = s.read(v);
          // -- if arg is an expression, create a new symbolic constant
          // -- to represent it
          if (bind::IsConst()(argV)) {
            args.push_back (argV);
          } else {
            // -- create symbolic constant u and make it equal argument value
            Expr u = s.havoc(v);
            args.push_back(u);
            side.push_back(mk<EQ>(u, argV));
          }
        }
        allVars.insert (++args.begin (), args.end ());
        assert(std::all_of(allVars.begin(), allVars.end(), bind::IsConst()));
        Expr post = bind::fapp (step, args);


        Expr tau = mknary<AND> (mk<TRUE>(m_efac), side);
        expr::filter (tau, bind::IsConst(),
                      std::inserter (allVars, allVars.begin ()));

        LOG("seahorn", errs() << "Adding rule : "
            << *mk<IMPL> (boolop::land (pre, tau), post) << "\n";);
        m_db.addRule (allVars, boolop::limp (boolop::land (pre, tau), post));
      }
    }

    allVars.clear ();
    args.clear ();
    s.reset ();


    // Add error flag exit rules
    // bb (err, V) & err -> bb_exit (err , V)
    assert(exit);

    for (auto &BB : F)
    {
      if (&BB == exit) continue;

      // XXX Can optimize. Only need the rules for BBs that trip the
      // error flag (directly or indirectly)
      s.reset ();
      allVars.clear ();
      args.clear ();

      s.write (pc, mkTerm<expr::mpz_class> (bbOrder [&BB], m_efac));
      args.push_back (s.read (pc));
      for (const Expr &v : glive) args.push_back (s.read (v));
      allVars.insert (++args.begin (), args.end ());

      Expr pre = bind::fapp (step, args);
      pre = boolop::land (pre, s.read (m_sem.errorFlag (BB)));

      args.clear ();
      s.write (pc, mkTerm<expr::mpz_class> (bbOrder [exit], m_efac));
      args.push_back (s.read (pc));
      for (const Expr &v : glive) args.push_back (s.read (v));
      allVars.insert (++args.begin (), args.end ());

      Expr post = bind::fapp (step, args);
      m_db.addRule (allVars, boolop::limp (pre, post));
    }

    if (F.getName ().equals ("main"))
    {
      args.clear ();
      s.reset ();

      s.write (pc, mkTerm<expr::mpz_class> (bbOrder [exit], m_efac));
      args.push_back (s.read (pc));
      if (ls.live (exit).size () == 1)
        s.write (m_sem.errorFlag (*exit), mk<TRUE> (m_efac));
      for (const Expr &v : glive) args.push_back (s.read (v));
      m_db.addQuery (bind::fapp (step , args));
    }
    else if (m_interproc)
    {
      // the summary rule
      // exit(live_at_exit) & !error.flag ->
      //                  summary(true, false, false, regions, arguments, globals, return)

      args.clear ();
      allVars.clear ();

      s.write (pc, mkTerm<expr::mpz_class> (bbOrder [exit], m_efac));
      args.push_back (s.read (pc));
      for (const Expr &v : glive) args.push_back (s.read (v));
      allVars.insert (++args.begin (), args.end ());

      Expr pre = bind::fapp (step, args);
      pre = boolop::land (pre, boolop::lneg (s.read (m_sem.errorFlag (*exit))));

      Expr falseE = mk<FALSE> (m_efac);
      ExprVector postArgs {mk<TRUE> (m_efac), falseE, falseE};
      const FunctionInfo &fi = m_sem.getFunctionInfo (F);
      evalArgs (fi, m_sem, s, std::back_inserter (postArgs));
      std::copy_if (postArgs.begin () + 3, postArgs.end (),
                    std::inserter (allVars, allVars.begin ()),
                    bind::IsConst());
      Expr post = bind::fapp (fi.sumPred, postArgs);
      m_db.addRule (allVars, boolop::limp (pre, post));

      // the error rule
      // bb_exit (true, V) -> S(true, false, true, V)
      pre = boolop::land (pre->arg (0), s.read (m_sem.errorFlag (*exit)));
      postArgs [2] = mk<TRUE> (m_efac);
      post = bind::fapp (fi.sumPred, postArgs);
      m_db.addRule (allVars, boolop::limp (pre, post));
    }
    else if (!exit & m_interproc) assert (0);

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

    DenseMap<const BasicBlock*, unsigned> cpgOrder;
    // globally live
    ExprSet glive;

    unsigned idx = 0;
    for (const CutPoint &cp : cpg)
    {
      cpgOrder [&cp.bb ()] = idx++;

      auto &live = ls.live (&cp.bb ());
      glive.insert (live.begin (), live.end ());

      if (m_interproc) extractFunctionInfo (cp.bb ());
    }

    // -- process counter
    Expr pc = bind::intConst (mkTerm<std::string> ("flat.pc", m_efac));

    // -- step predicate. First argument is pc
    Expr step;

    {
      ExprVector sorts;
      sorts.reserve (glive.size () + 2);
      sorts.push_back (bind::typeOf (pc));
      for (auto &v : glive) sorts.push_back (bind::typeOf (v));
      sorts.push_back (mk<BOOL_TY> (m_efac));

      // the step function is
      Expr name = mkTerm<const Function*> (&F, m_efac);
      // avoid clash with the names of summaries
      if (m_interproc) name = variant::prime (name);

      step = bind::fdecl (name, sorts);
      m_db.registerRelation (step);
    }


    const BasicBlock &entry = F.getEntryBlock ();

    ExprSet allVars;
    ExprVector args;
    SymStore s (m_efac);


    s.write (pc, mkTerm<expr::mpz_class> ((unsigned long)cpgOrder [&entry], m_efac));
    args.push_back (s.read (pc));
    for (const Expr& v : glive) args.push_back (s.read (v));
    allVars.insert (++args.begin (), args.end ());

    Expr rule = bind::fapp (step, args);
    rule = boolop::limp (boolop::lneg (s.read (m_sem.errorFlag (entry))), rule);
    m_db.addRule (allVars, rule);
    allVars.clear ();

    VCGen vcgen(m_sem);

    for (const CutPoint &cp : cpg)
      {
        for (const CpEdge *edge : boost::make_iterator_range (cp.succ_begin (),
                                                              cp.succ_end ()))
        {
          allVars.clear ();
          args.clear ();
          s.reset ();

          s.write (pc, mkTerm<expr::mpz_class> ((unsigned long)cpgOrder [&cp.bb ()], m_efac));
          args.push_back (s.read (pc));
          for (const Expr &v : glive) args.push_back (s.read (v));
          allVars.insert (++args.begin (), args.end ());

          Expr pre = bind::fapp (step, args);

          ExprVector side;
          side.push_back (boolop::lneg ((s.read (m_sem.errorFlag (cp.bb ())))));
          vcgen.genVcForCpEdgeLegacy(s, *edge, side);
          Expr tau = mknary<AND> (mk<TRUE> (m_efac), side);
          expr::filter (tau, bind::IsConst(),
                        std::inserter (allVars, allVars.begin ()));

          const BasicBlock &dst = edge->target ().bb ();
          args.clear ();

          s.write (pc, mkTerm<expr::mpz_class> ((unsigned long)cpgOrder [&dst], m_efac));
          args.push_back (s.read (pc));
          for (const Expr &v : glive) args.push_back (s.read (v));
          allVars.insert (++args.begin (), args.end ());

          Expr post = bind::fapp (step, args);
          m_db.addRule (allVars, boolop::limp (boolop::land (pre, tau), post));
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

      s.write (pc, mkTerm<expr::mpz_class> ((unsigned long)cpgOrder [&cp.bb ()], m_efac));
      args.push_back (s.read (pc));
      for (const Expr &v : glive) args.push_back (s.read (v));
      allVars.insert (++args.begin (), args.end ());

      Expr pre = bind::fapp (step, args);
      pre = boolop::land (pre, s.read (m_sem.errorFlag (cp.bb ())));

      args.clear ();

      s.write (pc, mkTerm<expr::mpz_class> ((unsigned long)cpgOrder [exit], m_efac));
      args.push_back (s.read (pc));
      for (const Expr &v : glive) args.push_back (s.read (v));
      allVars.insert (++args.begin (), args.end ());

      Expr post = bind::fapp (step, args);
      m_db.addRule (allVars, boolop::limp (pre, post));
    }

    if (F.getName ().equals ("main"))
    {
      args.clear ();
      s.reset ();

      s.write (pc, mkTerm<expr::mpz_class> ((unsigned long)cpgOrder [exit], m_efac));
      args.push_back (s.read (pc));
      if (ls.live (exit).size () == 1)
        s.write (m_sem.errorFlag (*exit), mk<TRUE> (m_efac));
      for (const Expr &v : glive) args.push_back (s.read (v));

      m_db.addQuery (bind::fapp (step , args));
    }
    else if (m_interproc)
    {
      // the summary rule
      // exit(live_at_exit) & !error.flag ->
      //     summary(true, false, false, regions, arguments, globals, return)

      args.clear ();
      allVars.clear ();

      s.write (pc, mkTerm<expr::mpz_class> ((unsigned long)cpgOrder [exit], m_efac));
      args.push_back (s.read (pc));
      for (const Expr &v : glive) args.push_back (s.read (v));
      allVars.insert (++args.begin (), args.end ());

      Expr pre = bind::fapp (step, args);
      pre = boolop::land (pre, boolop::lneg (s.read (m_sem.errorFlag (*exit))));

      Expr falseE = mk<FALSE> (m_efac);
      ExprVector postArgs {mk<TRUE> (m_efac), falseE, falseE};
      const FunctionInfo &fi = m_sem.getFunctionInfo (F);
      evalArgs (fi, m_sem, s, std::back_inserter (postArgs));
      std::copy_if (postArgs.begin () + 3, postArgs.end (),
                    std::inserter (allVars, allVars.begin ()),
                    bind::IsConst());
      Expr post = bind::fapp (fi.sumPred, postArgs);
      m_db.addRule (allVars, boolop::limp (pre, post));

      // the error rule
      // bb_exit (true, V) -> S(true, false, true, V)
      pre = boolop::land (pre->arg (0), s.read (m_sem.errorFlag (*exit)));
      postArgs [2] = mk<TRUE> (m_efac);
      post = bind::fapp (fi.sumPred, postArgs);
      m_db.addRule (allVars, boolop::limp (pre, post));
    }
    else if (!exit & m_interproc) assert (0);
  }
}
