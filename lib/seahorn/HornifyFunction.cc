#include "seahorn/HornifyFunction.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/LiveSymbols.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/ExprSeahorn.hh"
#include "seahorn/Support/Stats.hh"
#include "seahorn/Transforms/Instrumentation/GeneratePartialFnPass.hh"

#include "seahorn/Support/SeaDebug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"

static llvm::cl::opt<bool>
    ReduceFalse("horn-reduce-constraints",
                llvm::cl::desc("Reduce false constraints"),
                llvm::cl::init(false));
static llvm::cl::opt<bool>
    FlattenBody("horn-flatten",
                llvm::cl::desc("Flatten bodies of generated rules"),
                llvm::cl::init(false));

static llvm::cl::opt<bool>
    ReduceWeak("horn-reduce-weakly",
               llvm::cl::desc("Use weak solver for reducing constraints"),
               llvm::cl::init(true));

namespace seahorn {

void HornifyFunction::extractFunctionInfo(const BasicBlock &BB) {
  // --- Checks if the function requires a summary.

  const Function &F = *BB.getParent();
  // main does not need a summary
  if (F.getName().equals("main"))
    return;

  const ReturnInst *ret = dyn_cast<const ReturnInst>(BB.getTerminator());
  // not an exit block
  if (!ret)
    return;

  // --- The properties of BB determine what arguments it requires. The
  // following lambdas factor out routines for argument extraction so that they
  // can be conditionally enabled, based on BB.

  // Appends arguments to sorts for memory regions in fi.
  auto computeArgumentsFromMemoryRegions = [&](FunctionInfo &fi,
                                               ExprVector &sorts) {
    for (const Instruction &inst : BB) {
      if (const CallInst *ci = dyn_cast<const CallInst>(&inst)) {
        CallSite CS(const_cast<CallInst *>(ci));
        const Function *cf = CS.getCalledFunction();
        if (cf && (cf->getName().equals("shadow.mem.in") ||
                   cf->getName().equals("shadow.mem.out"))) {
          const Value &v = *CS.getArgument(1);
          Expr r = m_sem.symb(v);
          if (!r)
            continue;
          fi.regions.push_back(&v);
          sorts.push_back(bind::typeOf(r));
        }
      }
    }
  };

  // Appends arguments to sorts for arguments in fi.
  auto computeArgumentsFromDeclaration = [&](FunctionInfo &fi,
                                             ExprVector &sorts,
                                             bool filterForLiveness) {
    const ExprVector &live = m_parent.live(BB);
    for (const Argument &arg : F.args()) {
      if (filterForLiveness && !m_sem.isTracked(arg))
        continue;
      Expr v = m_sem.symb(arg);
      if (!v)
        continue;

      if (filterForLiveness && !std::binary_search(live.begin(), live.end(), v))
        continue;

      fi.args.push_back(&arg);
      sorts.push_back(bind::typeOf(v));
    }
  };

  // Appends arguments to sorts for globals.
  auto computeArgumentsFromGlobals = [&](FunctionInfo &fi, ExprVector &sorts) {
    const ExprVector &live = m_parent.live(BB);
    for (Expr v : live) {
      Expr u = bind::fname(bind::fname(v));
      if (!isOpX<VALUE>(u))
        continue;

      const Value *val = getTerm<const Value *>(u);
      if (!m_sem.isTracked(*val))
        continue;
      if (const GlobalVariable *gv = dyn_cast<const GlobalVariable>(val)) {
        fi.globals.push_back(gv);
        sorts.push_back(bind::typeOf(v));
      }
    }
  };

  /// --- Performs argument extraction.

  FunctionInfo &fi = m_sem.getFunctionInfo(F);
  fi.isInferable = isInferable(F);

  // reserved arguments:
  //  1. enabled flag
  //  2. incoming value of error.flag
  //  3. outgoing value of error.flag
  Expr boolSort = sort::boolTy(m_efac);
  ExprVector sorts{boolSort, boolSort, boolSort};

  if (fi.isInferable) {
    computeArgumentsFromDeclaration(fi, sorts, false);
  } else {
    computeArgumentsFromMemoryRegions(fi, sorts);
    computeArgumentsFromDeclaration(fi, sorts, true);
    computeArgumentsFromGlobals(fi, sorts);
  }

  // return value
  fi.ret = ret->getReturnValue();
  if (fi.ret) {
    // evaluate return value and get the sort from the value
    Expr v = m_sem.symb(*fi.ret);
    if (v)
      sorts.push_back(bind::typeOf(v));
    else
      fi.ret = NULL; // not tracked
  }

  sorts.push_back(mk<BOOL_TY>(m_efac));
  fi.sumPred = bind::fdecl(mkTerm<const Function *>(&F, m_efac), sorts);

  m_db.registerRelation(fi.sumPred);

  // --- Generates function summaries.

  // basic rules
  // if error.flag is on, it remains on, even if S is disabled
  //   S (true, true, true, V).
  //   S (false, true, true, V).
  // if S is disabled, error.flag is unchanged
  //   S (false, false, false, V).
  SymStore s(m_efac);
  ExprSet allVars;
  Expr trueE = mk<TRUE>(m_efac);
  Expr falseE = mk<FALSE>(m_efac);
  ExprVector postArgs{trueE, trueE, trueE};
  evalArgs(fi, m_sem, s, std::back_inserter(postArgs));
  // -- use a mutable gate to put everything together
  expr::filter(mknary<OUT_G>(postArgs), bind::IsConst(),
               std::inserter(allVars, allVars.begin()));

  m_db.addRule(allVars, bind::fapp(fi.sumPred, postArgs));

  postArgs[0] = falseE;
  m_db.addRule(allVars, bind::fapp(fi.sumPred, postArgs));

  postArgs[1] = falseE;
  postArgs[2] = falseE;
  m_db.addRule(allVars, bind::fapp(fi.sumPred, postArgs));

  auto addRuleForBasicSummaryProperties = [&]() {
    postArgs[0] = bind::boolConst(mkTerm(std::string("arg.0"), m_efac));
    postArgs[1] = bind::boolConst(mkTerm(std::string("arg.1"), m_efac));
    postArgs[2] = bind::boolConst(mkTerm(std::string("arg.2"), m_efac));
    m_db.addConstraint(
        bind::fapp(fi.sumPred, postArgs),
        mk<AND>(
            mk<OR>(postArgs[0], mk<EQ>(postArgs[1], postArgs[2])),
            mk<OR>(mk<NEG>(postArgs[0]), mk<NEG>(postArgs[1]), postArgs[2])));
  };
  if (!fi.isInferable)
    addRuleForBasicSummaryProperties();
}

llvm::SmallVector<llvm::CallInst *, 8>
HornifyFunction::getPartialFnsToSynth(Function &F) {
  // Gets reference to sea.synth.assert.
  if (!m_synthAssertFn) {
    auto &SBI = m_parent.getSBI();
    auto &M = (*F.getParent());
    m_synthAssertFn = SBI.mkSeaBuiltinFn(SeaBuiltinsOp::SYNTH_ASSERT, M);
  }

  // Records all functions passed to sea.synth.assert within BB.
  llvm::SmallVector<llvm::CallInst *, 8> partials;
  for (auto user : m_synthAssertFn->users()) {
    if (auto CI = dyn_cast<CallBase>(user)) {
      // Filters out calls that are in other blocks from the module.
      if (CI->getParent()->getParent() == &F) {
        auto *partial = dyn_cast<CallInst>(CI->getArgOperand(0));
        partials.push_back(partial);
        assert(partial);
        assert(partial->getCalledFunction()->getReturnType());
        assert(partial->getCalledFunction()->getReturnType()->isIntegerTy(1));
      }
    }
  }

  return partials;
}

void HornifyFunction::expandEdgeFilter(const llvm::Instruction &I) {
  m_sem.addToFilter(I);
  if (!isa<PHINode>(&I)) {
    // An instruction can depend on instructions from prior blocks. If the prior
    // instructions are not added to the filter, then the operation semantics
    // may encounter an undefined value. Therefore, they are added to the
    // filter.
    //
    // Note that it is not safe to include the operands of PHI nodes, and that
    // omitting PHI nodes is safe. If a block is recursive, then the PHI node
    // may depend on a "future" instruction from further into the block.
    // Furthermore, a PHI node is implemented using argument passing within the
    // CHCs, and therefore, the operands do not appear in the edge's transition
    // relation.
    for (auto &operand : I.operands()) {
      auto v = operand.get();
      if (isa<Instruction>(v))
        m_sem.addToFilter(*v);
    }
  }
}

void SmallHornifyFunction::mkBBSynthRules(const LiveSymbols &ls, Function &F,
                                          SymStore &store) {
  // Finds all instances of sea.synth.assert in F. Only the basis blocks that
  // make use of sea.synth.assert will be analyzed.
  auto partials = getPartialFnsToSynth(F);
  if (partials.empty())
    return;

  // Generates a rule for each assertion. Note that the order of instructions in
  // partials may not agree with the order of instructions in BB. This is due to
  // the order of users returned by Value::users().
  for (auto *partial : partials) {
    auto &BB = (*partial->getParent());

    // Searches for a matching instruction.
    bool found = false;
    for (auto itr = BB.begin(); itr != BB.end(); ++itr) {
      auto &I = (*itr);

      found = (partial == &I);
      if (found) {
        const ExprVector &live = ls.live(&BB);

        ExprSet vars;
        for (const Expr &v : live)
          vars.insert(store.read(v));

        Expr pre = store.eval(bind::fapp(m_parent.bbPredicate(BB), live));

        // Generates the VC for all instructions up to, but not including, I.
        // Remark: If I == BB.begin(), then the filter is empty.
        ExprVector lhs;
        lhs.push_back(boolop::lneg((store.read(m_sem.errorFlag(BB)))));
        if (itr != BB.begin())
          m_sem.exec(store, BB, lhs, mk<TRUE>(m_efac));

        // Assembles the function call associated with I.
        // TODO: improve robustness; exec on I must produce a single term.
        ExprVector rhs;
        expandEdgeFilter(I);
        m_sem.execRange(store, itr, std::next(itr), rhs, mk<TRUE>(m_efac));
        assert(rhs.size() == 1);
        Expr post = rhs.back();

        // Assume a-priori that the partial function call returns true.
        // This must came after rhs, else there can be two rv's for I.
        auto rv = m_sem.lookup(store, I);
        lhs.push_back(mk<EQ>(rv, mk<TRUE>(m_efac)));
        Expr tau = mknary<AND>(mk<TRUE>(m_efac), lhs);

        expr::filter(tau, bind::IsConst(), std::inserter(vars, vars.begin()));
        expr::filter(post, bind::IsConst(), std::inserter(vars, vars.begin()));

        auto rule = boolop::limp(boolop::land(pre, tau), post);
        LOG("seahorn", errs() << "Adding synthesis rule: " << (*rule) << "\n";);
        m_db.addRule(vars, rule);

        store.clear();
        m_sem.resetFilter();
        break;
      }

      expandEdgeFilter(I);
    }
    assert(found);
  }
}

void SmallHornifyFunction::runOnFunction(Function &F) {

  if (m_sem.isAbstracted(F))
    return;

  const BasicBlock *exit = findExitBlock(F);
  if (!exit) {
    WARN << "the exit block of function " << F.getName() << " is unreachable";
    return;
  }

  DenseMap<const BasicBlock *, Expr> pred;
  ExprVector sorts;

  const LiveSymbols &ls = m_parent.getLiveSybols(F);

  for (auto &BB : F) {
    // create predicate for the basic block
    Expr decl = m_parent.bbPredicate(BB);
    // register with fixedpoint
    m_db.registerRelation(decl);

    // -- attempt to extract FunctionInfo record from the current basic block
    // -- only succeeds if the current basic block is the last one
    // -- also constructs summary predicates
    if (m_interproc)
      extractFunctionInfo(BB);
  }

  // If F is an partial function stub, it should not have a body.
  const FunctionInfo &fi = m_sem.getFunctionInfo(F);
  if (fi.isInferable) {
    LOG("seahorn", errs() << "Omitting body of partial fn stub: "
                          << F.getName().str() << "\n");
    return;
  }

  BasicBlock &entry = F.getEntryBlock();
  ExprSet allVars;
  ExprVector args;
  SymStore s(m_efac);
  for (const Expr &v : ls.live(&F.getEntryBlock()))
    allVars.insert(s.read(v));
  Expr rule = s.eval(bind::fapp(m_parent.bbPredicate(entry), ls.live(&entry)));
  rule = boolop::limp(boolop::lneg(s.read(m_sem.errorFlag(entry))), rule);
  m_db.addRule(allVars, rule);
  allVars.clear();

  ExprVector side;
  for (auto &BB : F) {
    const BasicBlock *bb = &BB;
    for (const BasicBlock *dst : succs(*bb)) {
      allVars.clear();
      s.reset();
      side.clear();
      args.clear();

      const ExprVector &live = ls.live(bb);
      for (const Expr &v : live)
        allVars.insert(s.read(v));

      Expr pre = s.eval(bind::fapp(m_parent.bbPredicate(BB), live));
      side.push_back(boolop::lneg((s.read(m_sem.errorFlag(BB)))));
      m_sem.execEdg(s, BB, *dst, side);

      Expr tau = mknary<AND>(mk<TRUE>(m_efac), side);

      expr::filter(tau, bind::IsConst(),
                   std::inserter(allVars, allVars.begin()));
      for (const Expr &v : ls.live(dst))
        args.push_back(s.read(v));
      // -- use a mutable gate to put everything together
      expr::filter(mknary<OUT_G>(args), bind::IsConst(),
                   std::inserter(allVars, allVars.begin()));

      Expr post;
      post = s.eval(bind::fapp(m_parent.bbPredicate(*dst), ls.live(dst)));

      LOG("seahorn",
          errs() << "Adding rule : " << *mk<IMPL>(boolop::land(pre, tau), post)
                 << "\n";);
      m_db.addRule(allVars, boolop::limp(boolop::land(pre, tau), post));
    }
  }

  allVars.clear();
  side.clear();
  s.reset();

  // Generates rules for synthesis.
  mkBBSynthRules(ls, F, s);

  // Add error flag exit rules
  // bb (err, V) & err -> bb_exit (err , V)
  assert(exit);

  for (auto &BB : F) {
    if (&BB == exit)
      continue;

    // XXX Can optimize. Only need the rules for BBs that trip the
    // error flag (directly or indirectly)
    s.reset();
    allVars.clear();
    args.clear();
    const ExprVector &live = ls.live(&BB);
    for (const Expr &v : live)
      allVars.insert(s.read(v));
    Expr pre = s.eval(bind::fapp(m_parent.bbPredicate(BB), live));
    pre = boolop::land(pre, s.read(m_sem.errorFlag(BB)));

    for (const Expr &v : ls.live(exit))
      allVars.insert(s.read(v));
    Expr post = s.eval(bind::fapp(m_parent.bbPredicate(*exit), ls.live(exit)));
    m_db.addRule(allVars, boolop::limp(pre, post));
  }

  if (F.getName().equals("main") && ls.live(exit).size() == 1)
    m_db.addQuery(bind::fapp(m_parent.bbPredicate(*exit), mk<TRUE>(m_efac)));
  else if (F.getName().equals("main") && ls.live(exit).size() == 0)
    m_db.addQuery(bind::fapp(m_parent.bbPredicate(*exit)));
  else if (m_interproc) {
    // the summary rule
    // exit(live_at_exit) & !error.flag ->
    //                  summary(true, false, false, regions, arguments, globals,
    //                  return)

    const ExprVector &live = ls.live(exit);
    for (const Expr &v : live)
      allVars.insert(s.read(v));
    Expr pre = s.eval(bind::fapp(m_parent.bbPredicate(*exit), live));
    pre = boolop::land(pre, boolop::lneg(s.read(m_sem.errorFlag(*exit))));

    Expr falseE = mk<FALSE>(m_efac);
    ExprVector postArgs{mk<TRUE>(m_efac), falseE, falseE};
    evalArgs(fi, m_sem, s, std::back_inserter(postArgs));
    // -- use a mutable gate to put everything together
    expr::filter(mknary<OUT_G>(postArgs), bind::IsConst(),
                 std::inserter(allVars, allVars.begin()));

    Expr post = bind::fapp(fi.sumPred, postArgs);
    m_db.addRule(allVars, boolop::limp(pre, post));

    // the error rule
    // bb_exit (true, V) -> S(true, false, true, V)
    pre = boolop::land(pre->arg(0), s.read(m_sem.errorFlag(*exit)));
    postArgs[2] = mk<TRUE>(m_efac);
    post = bind::fapp(fi.sumPred, postArgs);
    m_db.addRule(allVars, boolop::limp(pre, post));
  } else if (!exit & m_interproc)
    assert(0);
}

namespace {

/// \brief Returns all successor edges of \p cp that contain the basic block
/// \c target between the source and destination (inclusively).
llvm::SmallVector<const CpEdge *, 8>
filterCpEdgesByBB(const CutPoint &cp, llvm::BasicBlock &target) {
  llvm::SmallVector<const CpEdge *, 8> matchingEdges;
  for (auto *e : llvm::make_range(cp.succ_begin(), cp.succ_end())) {
    for (auto &BB : *e) {
      if (&BB == &target) {
        matchingEdges.push_back(e);
        break;
      }
    }
  }
  return matchingEdges;
}

} // namespace

bool LargeHornifyFunction::mkEdgeSynthRules(const LiveSymbols &ls,
                                            const CallInst &partial,
                                            const CpEdge &edge,
                                            BasicBlock &target, VCGen &vcgen,
                                            SymStore &store) {
  for (auto &BB : edge) {
    if (&BB == &target)
      break;
    for (auto &I : BB)
      expandEdgeFilter(I);
  }

  // Uses iterators rather than `for (auto I : target)` since an iterator is
  // required by execRange.
  const BasicBlock &source = edge.source().bb();
  const ExprVector &live = ls.live(&source);
  for (auto itr = target.begin(), end = target.end(); itr != end; ++itr) {
    auto &I = (*itr);

    if (&partial == &I) {
      // The cut points `src` and `dst` should not appear in `cpg` as they are
      // temporary. For this reason, the CP's are minimally initialized for use
      // by `genVcForCpEdgeLegacy`. Note that at the time of writing this code,
      // `genVcForCpEdgeLegacy` relies only on `src.id()`, `src.bb()`, and
      // `dst.bb()`.
      CutPoint src(edge.parent(), edge.source().id(), source);
      CutPoint dst(edge.parent(), 0, target);
      CpEdge truncatedEdge(src, dst);
      for (auto &BB : edge) {
        truncatedEdge.push_back(&BB);
        if (&BB == &dst.bb())
          break;
      }

      ExprSet vars;
      ExprVector args;
      for (const Expr &v : live)
        args.push_back(store.read(v));
      vars.insert(args.begin(), args.end());

      Expr pre = bind::fapp(m_parent.bbPredicate(source), args);

      // Generates the VC for all instructions up to, but not including, I.
      ExprVector lhs;
      bool isFirstBlock = (&*truncatedEdge.begin() == &target);
      lhs.push_back(boolop::lneg((store.read(m_sem.errorFlag(source)))));
      if (!isFirstBlock || (itr != target.begin()))
        vcgen.genVcForCpEdgeLegacy(store, truncatedEdge, lhs, false);

      // Assembles the function call associated with I.
      ExprVector rhs;
      expandEdgeFilter(I);
      m_sem.execRange(store, itr, std::next(itr), rhs, mk<TRUE>(m_efac));
      assert(rhs.size() == 1);
      Expr post = rhs.back();

      // Asserts that the intermediate block is reached.
      if (!isFirstBlock)
        lhs.push_back(store.read(m_sem.symb(target)));

      // Assume a-priori that the partial function call returns true.
      // This must came after rhs, else there can be two rv's for I.
      auto rv = m_sem.lookup(store, I);
      lhs.push_back(mk<EQ>(rv, mk<TRUE>(m_efac)));
      Expr tau = mknary<AND>(mk<TRUE>(m_efac), lhs);

      expr::filter(tau, bind::IsConst(), std::inserter(vars, vars.begin()));
      expr::filter(post, bind::IsConst(), std::inserter(vars, vars.begin()));

      auto rule = boolop::limp(boolop::land(pre, tau), post);
      LOG("seahorn", errs() << "Adding synthesis rule: " << (*rule) << "\n";);
      m_db.addRule(vars, rule);

      return true;
    }

    expandEdgeFilter(I);
  }

  return false;
}

void LargeHornifyFunction::runOnFunction(Function &F) {
  ScopedStats _st_("LargeHornifyFunction");

  if (m_sem.isAbstracted(F))
    return;

  const BasicBlock *exit = findExitBlock(F);
  if (!exit) {
    WARN << "the exit block of function " << F.getName() << " is unreachable";
    return;
  }

  LOG("reduce", errs() << "Begin HornifyFunction: " << F.getName() << "\n";);

  CutPointGraph &cpg = m_parent.getCpg(F);
  const LiveSymbols &ls = m_parent.getLiveSybols(F);

  ExprVector sorts;

  for (const CutPoint &cp : cpg) {
    Expr decl = m_parent.bbPredicate(cp.bb());
    m_db.registerRelation(decl);
    if (m_interproc)
      extractFunctionInfo(cp.bb());
  }

  const FunctionInfo &fi = m_sem.getFunctionInfo(F);
  if (fi.isInferable) {
    LOG("seahorn", errs() << "Omitting body of partial fn stub: "
                          << F.getName().str() << "\n");
    return;
  }

  const BasicBlock &entry = F.getEntryBlock();

  ExprSet allVars;
  ExprVector args;
  SymStore s(m_efac);
  for (const Expr &v : ls.live(&entry))
    args.push_back(s.read(v));
  allVars.insert(args.begin(), args.end());

  Expr rule = bind::fapp(m_parent.bbPredicate(entry), args);
  rule = boolop::limp(boolop::lneg(s.read(m_sem.errorFlag(entry))), rule);
  m_db.addRule(allVars, rule);
  allVars.clear();
  ZSolver<EZ3> smt(m_zctx);

  /** use a rather weak solver */
  ZParams<EZ3> params(m_zctx);
  // -- always use weak arrays for now
  params.set(":smt.array.weak", true);
  if (ReduceWeak)
    params.set(":smt.arith.ignore_int", true);
  smt.set(params);

  VCGen vcgen(m_sem);

  DenseSet<const BasicBlock *> reached;
  reached.insert(&cpg.begin()->bb());

  unsigned rule_cnt = 0;
  for (const CutPoint &cp : cpg) {
    if (reached.count(&cp.bb()) <= 0)
      continue;

    for (const CpEdge *edge :
         boost::make_iterator_range(cp.succ_begin(), cp.succ_end())) {
      allVars.clear();
      args.clear();
      s.reset();
      const ExprVector &live = ls.live(&cp.bb());

      for (const Expr &v : live)
        args.push_back(s.read(v));
      allVars.insert(args.begin(), args.end());

      Expr pre = bind::fapp(m_parent.bbPredicate(cp.bb()), args);

      ExprVector side;
      side.push_back(boolop::lneg((s.read(m_sem.errorFlag(cp.bb())))));
      vcgen.genVcForCpEdgeLegacy(s, *edge, side);
      Expr tau = mknary<AND>(mk<TRUE>(m_efac), side);
      expr::filter(tau, bind::IsConst(),
                   std::inserter(allVars, allVars.begin()));

      const BasicBlock &dst = edge->target().bb();
      args.clear();
      for (const Expr &v : ls.live(&dst))
        args.push_back(s.read(v));
      // -- use a mutable gate to put everything together
      expr::filter(mknary<OUT_G>(args), bind::IsConst(),
                   std::inserter(allVars, allVars.begin()));
      // allVars.insert (args.begin (), args.end ());

      if (ReduceFalse) {
        ScopedStats __st__("HornifyFunction.reduce-false");
        Stats::count("HornifyFunction.edge");
        bind::IsConst isConst;
        for (auto &e : side) {
          // ignore uninterpreted functions, makes the problem easier to solve
          if (!bind::isFapp(e) || isConst(e))
            smt.assertExpr(e);
        }
        LOG(
            "reduce",

            std::error_code EC;
            raw_fd_ostream file("/tmp/edge.smt2", EC, sys::fs::F_Text);
            if (!EC) {
              file << "(set-info :original \"" << edge->source().bb().getName()
                   << " --> " << edge->target().bb().getName() << "\")\n";
              smt.toSmtLib(file);
              file.close();
            });
        auto res = smt.solve();

        smt.reset();

        if (!res)
          LOG("reduce", errs() << "Reduced edge to false: "
                               << edge->source().bb().getName() << " --> "
                               << edge->target().bb().getName() << "\n";);
        else
          LOG("reduce", errs() << "NOT Reduced edge to false: "
                               << edge->source().bb().getName() << " --> "
                               << edge->target().bb().getName() << "\n";);

        if (!res) {
          Stats::count("HornifyFunction.edge.false");
          continue; /* skip a rule with an inconsistent body */
        }
      }

      reached.insert(&dst);
      Expr post = bind::fapp(m_parent.bbPredicate(dst), args);
      Expr body = boolop::land(pre, tau);
      // flatten body if needed
      if (FlattenBody && isOpX<AND>(body) && body->arity() == 2 &&
          isOpX<AND>(body->arg(1))) {
        ExprVector v;
        v.reserve(1 + body->arg(1)->arity());
        v.push_back(body->arg(0));
        body = body->arg(1);
        for (unsigned i = 0; i < body->arity(); ++i)
          v.push_back(body->arg(i));

        body = mknary<AND>(mk<TRUE>(m_efac), v);
      }

      m_db.addRule(allVars, boolop::limp(body, post));
    }
  }

  allVars.clear();
  args.clear();
  s.reset();

  // Add error flag exit rules
  // bb (err, V) & err -> bb_exit (err , V)
  assert(exit);

  for (const CutPoint &cp : cpg) {
    if (&cp.bb() == exit)
      continue;

    // XXX Can optimize. Only need the rules for BBs that trip the
    // error flag (directly or indirectly)
    s.reset();
    allVars.clear();
    args.clear();

    const ExprVector &live = ls.live(&cp.bb());
    for (const Expr &v : live)
      args.push_back(s.read(v));
    allVars.insert(args.begin(), args.end());

    Expr pre = bind::fapp(m_parent.bbPredicate(cp.bb()), args);
    pre = boolop::land(pre, s.read(m_sem.errorFlag(cp.bb())));

    args.clear();
    for (const Expr &v : ls.live(exit))
      args.push_back(s.read(v));
    allVars.insert(args.begin(), args.end());

    Expr post = bind::fapp(m_parent.bbPredicate(*exit), args);
    m_db.addRule(allVars, boolop::limp(pre, post));
  }

  // Generates synthesis rules for each call to sea.synth.assert.
  s.reset();
  for (auto partial : getPartialFnsToSynth(F)) {
    for (auto &cp : cpg) {
      auto &srcBB = cp.bb();
      if (reached.count(&srcBB) <= 0)
        continue;

      auto &targetBB = (*partial->getParent());
      for (auto *e : filterCpEdgesByBB(cp, targetBB)) {
        bool success = mkEdgeSynthRules(ls, *partial, *e, targetBB, vcgen, s);
        assert(success);
        s.reset();
        m_sem.resetFilter();
      }
    }
  }

  if (F.getName().equals("main") && ls.live(exit).size() == 1)
    m_db.addQuery(bind::fapp(m_parent.bbPredicate(*exit), mk<TRUE>(m_efac)));
  else if (F.getName().equals("main") && ls.live(exit).size() == 0)
    m_db.addQuery(bind::fapp(m_parent.bbPredicate(*exit)));
  else if (m_interproc) {
    // the summary rule
    // exit(live_at_exit) & !error.flag ->
    //     summary(true, false, false, regions, arguments, globals, return)

    args.clear();
    allVars.clear();

    const ExprVector &live = ls.live(exit);
    for (const Expr &v : live)
      args.push_back(s.read(v));
    allVars.insert(args.begin(), args.end());

    Expr pre = bind::fapp(m_parent.bbPredicate(*exit), args);
    pre = boolop::land(pre, boolop::lneg(s.read(m_sem.errorFlag(*exit))));

    Expr falseE = mk<FALSE>(m_efac);
    ExprVector postArgs{mk<TRUE>(m_efac), falseE, falseE};
    evalArgs(fi, m_sem, s, std::back_inserter(postArgs));
    // -- use a mutable gate to put everything together
    expr::filter(mknary<OUT_G>(postArgs), bind::IsConst(),
                 std::inserter(allVars, allVars.begin()));
    Expr post = bind::fapp(fi.sumPred, postArgs);
    m_db.addRule(allVars, boolop::limp(pre, post));

    // the error rule
    // bb_exit (true, V) -> S(true, false, true, V)
    pre = boolop::land(pre->arg(0), s.read(m_sem.errorFlag(*exit)));
    postArgs[2] = mk<TRUE>(m_efac);
    post = bind::fapp(fi.sumPred, postArgs);
    m_db.addRule(allVars, boolop::limp(pre, post));
  } else if (!exit & m_interproc)
    assert(0);

  LOG("reduce", errs() << "Done HornifyFunction: " << F.getName() << "\n";);
}

// bool HornifyFunction::checkProperty(ExprVector predicates, Expr &cex){
//   tribool res  = m_fp.query();
//   std::vector<std::string> invariants;
//   if (res){
//     errs() << "UNSAFE";
//     LOG("seahorn", errs() << "\nCEX\n");
//     //cex = m_fp.getCex();
//     LOG("seahorn", errs() << "\t" << m_zctx.toSmtLib(cex) << "\n");

//     return false;
//   }else if (!res){
//     errs() << "SAFE";
//     LOG("seahorn", errs() << "\nINVARIANTS");
//     for (Expr p: predicates){
//       Expr delta = m_fp.getCoverDelta(p);
//       if (!(isOpX<TRUE> (delta))) {
//         LOG("seahorn", errs() << "\t- BLOCK : " << m_zctx.toSmtLib(p) <<
//         "\n"); std::string inv = m_zctx.toSmtLib(delta); invariants.push_back
//         (inv); LOG("seahorn", errs() << "\t\t" << inv << "\n");
//       }
//     }
//     return true;
//   }else{
//     errs() <<"ERROR\n";
//     exit (1);
//   }
// }

} // namespace seahorn
