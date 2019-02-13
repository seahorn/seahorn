#include "seahorn/PathBasedBmc.hh"
#include "seahorn/Analysis/CutPointGraph.hh"
#include "seahorn/Support/CFG.hh"
#include "seahorn/UfoOpSem.hh"
#include "seahorn/config.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/Stats.hh"

#ifdef HAVE_CRAB_LLVM
#include "crab_llvm/CrabLlvm.hh"
#include "crab_llvm/HeapAbstraction.hh"
#include "crab_llvm/wrapper_domain.hh"
#include "seahorn/LoadCrab.hh"
#endif

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/unordered_map.hpp"

/**
  NOTE #1: certain parts of this implementation is VC
  encoding-dependent. For instance, the generation of blocking clauses
  and the boolean abstraction.

  NOTE #2: the BMC engines can be used in two scenarios: (1) for validating a
  CEX, and (2) for performing bounded-model checking rather than
  invariant generation.

  Sometimes, crab can fail at solving a path if it cannot build a
  single path from boolean literals. When BMC is used in context (1)
  this can be fixed by running SeaHorn with the options:

    --horn-split-only-critical=true
    --horn-at-most-one-predecessor=true

  These options are used by VCGen. Although BMC uses
  BvOpSem these options still can help since the CEX is first
  generated using VCGen. There is no an equivalent of
  --horn-at-most-one-predecessor for BvOpSem but we might want
  to implement it in the future in cases crab also fails in scenario
  (2).
**/

namespace seahorn {
// To tell BmcPass if we want crab enabled.
bool XHornBmcCrab;
} // namespace seahorn

static llvm::cl::opt<bool, true>
    UseCrab("horn-bmc-crab", llvm::cl::desc("Use of Crab in Path-based BMC"),
            llvm::cl::location(seahorn::XHornBmcCrab), llvm::cl::init(false));

#ifdef HAVE_CRAB_LLVM
static llvm::cl::opt<crab_llvm::CrabDomain> CrabDom(
    "horn-bmc-crab-dom",
    llvm::cl::desc("Crab Domain to solve path formulas in Path-Based BMC"),
    llvm::cl::values(clEnumValN(crab_llvm::INTERVALS, "int",
                                "Classical interval domain (default)"),
                     clEnumValN(crab_llvm::ZONES_SPLIT_DBM, "zones",
                                "Zones domain."),
                     clEnumValN(crab_llvm::TERMS_INTERVALS, "term-int",
                                "Intervals with uninterpreted functions."),
                     clEnumValN(crab_llvm::TERMS_ZONES, "rtz",
                                "Reduced product of term-dis-int and zones."),
                     clEnumValN(crab_llvm::WRAPPED_INTERVALS, "w-int",
                                "Wrapped interval domain")),
    llvm::cl::init(crab_llvm::INTERVALS));
#endif

// It has only effect if UseCrab is enabled.
static llvm::cl::opt<bool> UseCrabGlobalInvariants(
    "horn-bmc-crab-invariants",
    llvm::cl::desc("Load crab invariants into the Path-based BMC engine"),
    llvm::cl::init(true));

// It has only effect if UseCrab is enabled.
static llvm::cl::opt<bool> LayeredCrabSolving(
    "horn-bmc-crab-layered-solving",
    llvm::cl::desc("Try only-boolean reasoning before using "
                   "--horn-bmc-crab-dom to prove path unsatisfiability"),
    llvm::cl::init(false));

namespace bmc_detail {
enum muc_method_t {
  MUC_NONE,
  MUC_DELETION,
  MUC_ASSUMPTIONS,
  MUC_BINARY_SEARCH
};
}

static llvm::cl::opt<enum bmc_detail::muc_method_t> MucMethod(
    "horn-bmc-muc",
    llvm::cl::desc(
        "Method used to compute minimal unsatisfiable cores in Path-Based BMC"),
    llvm::cl::values(clEnumValN(bmc_detail::MUC_NONE, "none", "None"),
                     clEnumValN(bmc_detail::MUC_ASSUMPTIONS, "assume",
                                "Solving with assumptions"),
                     clEnumValN(bmc_detail::MUC_DELETION, "deletion",
                                "Deletion-based method"),
                     clEnumValN(bmc_detail::MUC_BINARY_SEARCH, "quickXplain",
                                "QuickXplain method")),
    llvm::cl::init(bmc_detail::MUC_ASSUMPTIONS));

static llvm::cl::opt<unsigned> PathTimeout(
    "horn-bmc-path-timeout",
    llvm::cl::desc(
        "Timeout (sec) for SMT solving a path formula in Path-based BMC"),
    llvm::cl::init(1800u));

static llvm::cl::opt<unsigned> MucTimeout(
    "horn-bmc-muc-timeout",
    llvm::cl::desc("Timeout (sec) for SMT query during MUC in Path-based BMC"),
    llvm::cl::init(5u));

static llvm::cl::opt<std::string> SmtOutDir(
    "horn-bmc-smt-outdir",
    llvm::cl::desc("Directory to dump path formulas in SMT-LIB format"),
    llvm::cl::init(""), llvm::cl::value_desc("directory"));

// To print messages with timestamps
static llvm::raw_ostream &get_os(bool show_time = false) {
  llvm::raw_ostream *result = &llvm::errs();
  if (show_time) {
    time_t now = time(0);
    struct tm tstruct;
    char buf[80];
    tstruct = *localtime(&now);
    strftime(buf, sizeof(buf), "[%Y-%m-%d.%X] ", &tstruct);
    *result << buf;
  }
  return *result;
}

namespace seahorn {

// Return true if e is a tuple
static bool isTuple(Expr e) {
  return expr::op::bind::isFdecl(e->left()) && isOpX<TUPLE>(e->left()->left());
}

// Retun the tuple elements as a pair
static std::pair<Expr, Expr> getTuple(Expr e) {
  assert(isTuple(e));
  Expr tuple = e->left()->left();
  Expr src = tuple->left();
  Expr dst = tuple->right();
  return std::make_pair(src, dst);
}

// Customized ordering to ensure that non-tuple expressions come
// first than tuple expressions, otherwise standard ordering between
// Expr's.
struct lessExpr {
  bool operator()(Expr e1, Expr e2) const {
    if (!isTuple(e1) && isTuple(e2))
      return true;
    else if (isTuple(e1) && !isTuple(e2))
      return false;
    else
      return e1 < e2;
  }
};

// A CFG edge is critical if it is not the only leaving its source
// block and the only entering to the destination block.
static bool isCriticalEdge(const BasicBlock *src, const BasicBlock *dst) {
  bool not_only_leaving = false;
  bool not_only_entering = false;

  for (const BasicBlock *s : seahorn::succs(*src)) {
    if (s != dst) {
      not_only_leaving = true;
      break;
    }
  }

  for (const BasicBlock *p : seahorn::preds(*dst)) {
    if (p != src) {
      not_only_entering = true;
      break;
    }
  }

  return (not_only_leaving && not_only_entering);
}

// Remove all boolean operators except AND/OR/NEG
struct PreNNF : public std::unary_function<Expr, Expr> {
  PreNNF() {}

  Expr operator()(Expr exp) {

    if (!isOp<BoolOp>(exp)) {
      return exp;
    }

    if (!isOpX<IMPL>(exp) && !isOpX<ITE>(exp) && !isOpX<IFF>(exp) &&
        !isOpX<XOR>(exp)) {
      return exp;
    }

    if (isOpX<XOR>(exp)) {
      assert(false && "TODO");
      return exp;
    } else if (isOpX<IMPL>(exp)) {
      return op::boolop::lor(op::boolop::lneg(exp->left()), exp->right());
    } else if (isOpX<ITE>(exp)) {
      assert(exp->arity() == 3);
      Expr c = exp->operator[](0);
      Expr e1 = exp->operator[](1);
      Expr e2 = exp->operator[](2);
      return op::boolop::lor(op::boolop::land(c, e1),
                             op::boolop::land(op::boolop::lneg(c), e2));
    } else {
      assert(isOpX<IFF>(exp));
      return op::boolop::land(
          op::boolop::lor(op::boolop::lneg(exp->left()), exp->right()),
          op::boolop::lor(op::boolop::lneg(exp->right()), exp->left()));
    }
  }
};

// Perform boolean abstraction
struct BA : public std::unary_function<Expr, VisitAction> {

  bool is_pos_bool_lit(Expr e) const {
    return (isOpX<TRUE>(e) || isOpX<FALSE>(e) || bind::isBoolConst(e));
  }

  bool is_neg_bool_lit(Expr e) const {
    return (isOpX<NEG>(e) && is_pos_bool_lit(e->left()));
  }

  bool is_bool_lit(Expr e) const {
    return (is_pos_bool_lit(e) || is_neg_bool_lit(e));
  }

  ExprFactory &efac;
  std::shared_ptr<op::boolop::TrivialSimplifier> r;

  BA(const BA &o) : efac(o.efac), r(o.r) {}

  BA(ExprFactory &fac)
      : efac(fac), r(std::make_shared<op::boolop::TrivialSimplifier>(efac)) {}

  // Pre: exp is in NNF
  VisitAction operator()(Expr exp) {
    if (is_pos_bool_lit(exp)) {
      return VisitAction::skipKids();
    }

    if (isOpX<NEG>(exp)) {
      if (is_pos_bool_lit(exp->left())) {
        return VisitAction::doKids();
      } else {
        return VisitAction::changeTo(r->trueE);
      }
    }

    if (isOpX<AND>(exp) || isOpX<OR>(exp)) {
      return VisitAction::doKids();
    }

    if (isOpX<EQ>(exp)) {
      if (is_bool_lit(exp->left()) && is_bool_lit(exp->right())) {
        return VisitAction::doKids();
      }
    }

    // everything else abstracted to true
    return VisitAction::changeTo(r->trueE);
  }
};

static Expr pre_nnf(Expr exp) {
  op::boolop::BS<PreNNF> bs(new PreNNF());
  return dagVisit(bs, exp);
}

static Expr bool_abstraction(Expr exp) {
  exp = pre_nnf(exp);
  exp = op::boolop::nnf(exp);
  BA n(exp->efac());
  return dagVisit(n, exp);
}

static void bool_abstraction(ExprVector &side, ExprVector &abs_side) {
  for (auto exp : side) {
    Expr bexp = bool_abstraction(exp);
    abs_side.push_back(bexp);
  }
  abs_side.erase(std::remove_if(abs_side.begin(), abs_side.end(),
                                [](Expr e) { return isOpX<TRUE>(e); }),
                 abs_side.end());
}

struct scoped_solver {
  ufo::ZSolver<ufo::EZ3> &m_solver;

public:
  scoped_solver(ufo::ZSolver<ufo::EZ3> &solver, unsigned timeout /* seconds*/)
      : m_solver(solver) {
    ufo::ZParams<ufo::EZ3> params(m_solver.getContext());
    // We should check here for possible overflow if timeout is
    // given, e.g., in miliseconds.
    params.set(":timeout", timeout * 1000);
    m_solver.set(params);
  }

  ~scoped_solver() {
    ufo::ZParams<ufo::EZ3> params(m_solver.getContext());
    params.set(":timeout", 4294967295u); // disable timeout
    m_solver.set(params);
  }

  ufo::ZSolver<ufo::EZ3> &get() { return m_solver; }
};

// Compute minimal unsatisfiable cores
class minimal_unsat_core {
protected:
  ufo::ZSolver<ufo::EZ3> &m_solver;

  std::vector<unsigned> m_size_solver_calls;

public:
  minimal_unsat_core(ufo::ZSolver<ufo::EZ3> &solver) : m_solver(solver) {}

  virtual void run(const ExprVector &f, ExprVector &core) = 0;

  virtual std::string get_name(void) const = 0;

  void print_stats(llvm::raw_ostream &o) {
    unsigned sz = m_size_solver_calls.size();
    unsigned avg = 0;

    if (sz > 0) {
      // compute average
      int tot = 0;
      for (unsigned i = 0, e = sz; i < e; ++i) {
        tot += m_size_solver_calls[i];
      }
      avg = (unsigned)tot / sz;
    }

    o << get_name() << ":\n";
    o << "\t" << sz << " number of solver calls\n";
    o << "\t" << avg << " average size of each query\n";
  }
};

class muc_with_assumptions : public minimal_unsat_core {
public:
  muc_with_assumptions(ufo::ZSolver<ufo::EZ3> &solver)
      : minimal_unsat_core(solver) {}

  std::string get_name(void) const { return "MUC with assumptions"; }

  void run(const ExprVector &f, ExprVector &core) override {
    const bool simplify = false;
    bmc_impl::unsat_core(m_solver, f, false, core);
  }
};

class binary_search_muc;

// Deletion deletion-based method
class deletion_muc : public minimal_unsat_core {
  friend class binary_search_muc;

private:
  typedef ExprVector::const_iterator const_iterator;
  boost::tribool check(const_iterator it, const_iterator et,
                       const ExprVector &assumptions) {
    m_solver.reset();
    for (Expr e : assumptions) {
      m_solver.assertExpr(e);
    }
    for (Expr e : boost::make_iterator_range(it, et)) {
      m_solver.assertExpr(e);
    }
    m_size_solver_calls.push_back(assumptions.size() + std::distance(it, et));
    boost::tribool res;
    {
      scoped_solver ss(m_solver, MucTimeout);
      res = ss.get().solve();
    }
    return res;
  }

  void run(const ExprVector &f, const ExprVector &assumptions,
           ExprVector &out) {
    assert(!((bool)check(f.begin(), f.end(), assumptions)));

    out.insert(out.end(), f.begin(), f.end());
    for (unsigned i = 0; i < out.size();) {
      Expr saved = out[i];
      out[i] = out.back();
      boost::tribool res = check(out.begin(), out.end() - 1, assumptions);
      if (res) {
        out[i++] = saved;
      } else if (!res) {
        out.pop_back();
      } else {
        // timeout
        out.assign(f.begin(), f.end());
        return;
      }
    }
  }

public:
  deletion_muc(ufo::ZSolver<ufo::EZ3> &solver) : minimal_unsat_core(solver) {}

  void run(const ExprVector &f, ExprVector &out) override {
    ExprVector assumptions;
    run(f, assumptions, out);
  }

  std::string get_name() const override { return "Deletion MUC"; }
};

// Compute minimal unsatisfiable cores using binary search
// Naive implementation of Junker's QuickXplain method.
class binary_search_muc : public minimal_unsat_core {
private:
  // minimum size of the formula to perform binary search on it
  const unsigned threshold = 5;

  typedef typename ExprVector::const_iterator const_iterator;
  typedef boost::iterator_range<const_iterator> const_range;

  boost::tribool check_with_assumptions(const_range f, const ExprVector &assume,
                                        const_range more_assume) {
    m_solver.reset();
    for (Expr e : f) {
      m_solver.assertExpr(e);
    }
    for (Expr e : assume) {
      m_solver.assertExpr(e);
    }
    for (Expr e : more_assume) {
      m_solver.assertExpr(e);
    }
    m_size_solver_calls.push_back(
        std::distance(f.begin(), f.end()) + assume.size() +
        std::distance(more_assume.begin(), more_assume.end()));
    boost::tribool res;
    {
      scoped_solver ss(m_solver, MucTimeout);
      res = ss.get().solve();
    }
    return res;
  }

  void run_with_assumptions(const_range f, const ExprVector &assume,
                            ExprVector &core) {
    ExprVector more_assume;
    run_with_assumptions(
        f, assume,
        boost::make_iterator_range(more_assume.begin(), more_assume.end()),
        core);
  }

  void run_with_assumptions(const_range f, const ExprVector &assume,
                            const_range more_assume, ExprVector &core) {
    assert(!(bool)check_with_assumptions(f, assume, more_assume));

    unsigned size = std::distance(f.begin(), f.end());
    if (size <= threshold) {
      if (size == 0) {
      } else if (size == 1) {
        // core.reserve(size);
        core.insert(core.end(), f.begin(), f.end());
      } else {
        deletion_muc muc(m_solver);
        ExprVector small_f(f.begin(), f.end());
        ExprVector small_core;
        muc.run(small_f, assume, small_core);
        core.insert(core.end(), small_core.begin(), small_core.end());
        m_size_solver_calls.insert(m_size_solver_calls.end(),
                                   muc.m_size_solver_calls.begin(),
                                   muc.m_size_solver_calls.end());
      }
      return;
    }
    const_iterator A_beg = f.begin();
    const_iterator A_end = f.begin() + (size / 2);
    const_iterator B_beg = A_end;
    const_iterator B_end = f.end();
    const_range A = boost::make_iterator_range(A_beg, A_end);
    const_range B = boost::make_iterator_range(B_beg, B_end);
    boost::tribool resA = boost::indeterminate;
    boost::tribool resB = boost::indeterminate;
    /*A*/
    resA = check_with_assumptions(A, assume, more_assume);
    if (!resA) {
      return run_with_assumptions(A, assume, more_assume, core);
    } else if (resA) {
      /* B */
      resB = check_with_assumptions(B, assume, more_assume);
      if (!resB) {
        return run_with_assumptions(B, assume, more_assume, core);
      } else if (resB) {
        /* do nothing */
      } else {
        // unknown
        core.assign(f.begin(), f.end());
        return;
      }
    } else {
      core.assign(f.begin(), f.end());
      return;
    }

    // minimize A wrt {assumptions, B}
    run_with_assumptions(A, assume, B, core);
    // minimize B wrt {assumptions, core}
    run_with_assumptions(
        B, assume, boost::make_iterator_range(core.begin(), core.end()), core);
  }

public:
  binary_search_muc(ufo::ZSolver<ufo::EZ3> &solver)
      : minimal_unsat_core(solver) {}

  void run(const ExprVector &f, ExprVector &out) override {
    ExprVector assume, more_assume;
    run_with_assumptions(
        boost::make_iterator_range(f.begin(), f.end()), assume,
        boost::make_iterator_range(more_assume.begin(), more_assume.end()),
        out);
  }

  std::string get_name() const override { return "QuickXplain"; }
};

#ifdef HAVE_CRAB_LLVM
/** Begin convert from crab invariants to SeaHorn Expr **/

// Map from basic blocks to linear constraints
// The map itself is hidden
struct crab_map {
  virtual ~crab_map() {}
  virtual crab_llvm::lin_cst_sys_t operator()(const BasicBlock *b) = 0;
};

class crab_global_map : public crab_map {
public:
  crab_global_map(crab_llvm::CrabLlvmPass &crab_global)
      : m_crab_global(crab_global) {}
  virtual crab_llvm::lin_cst_sys_t operator()(const BasicBlock *b) override {
    auto pre = m_crab_global.get_pre(b);
    if (pre) {
      return pre->to_linear_constraints();
    } else {
      // usually if pre is null then it's because the block is
      // unreachable. However, since we don't know for sure we just
      // return true.
      return crab_llvm::lin_cst_sys_t();
    }
  }

private:
  crab_llvm::CrabLlvmPass &m_crab_global;
};

class crab_path_map : public crab_map {
public:
  crab_path_map(typename crab_llvm::IntraCrabLlvm::invariant_map_t &inv_map)
      : m_map(inv_map) {}
  virtual crab_llvm::lin_cst_sys_t operator()(const BasicBlock *b) override {
    auto it = m_map.find(b);
    if (it != m_map.end()) {
      return it->second->to_linear_constraints();
    } else {
      // if the block is not found then the value is assumed to be
      // bottom.
      return crab_llvm::lin_cst_t::get_false();
    }
  }

private:
  typename crab_llvm::IntraCrabLlvm::invariant_map_t &m_map;
};

class crabToSea {
public:
  crabToSea(const LiveSymbols &ls, crab_llvm::HeapAbstraction &heap_abs,
            const Function &fn, ExprFactory &efac)
      : m_ls(ls), m_heap_abs(heap_abs), m_fn(fn), m_efac(efac) {}

  template <typename BBIterator, typename SeaMap>
  void convert(BBIterator beg, BBIterator end, crab_map &in, SeaMap &out) {

    for (const BasicBlock *b : boost::make_iterator_range(beg, end)) {
      const ExprVector &live = m_ls.live(b);
      LinConsToExpr conv(m_heap_abs, m_fn, live);
      crab_llvm::lin_cst_sys_t csts = in(b);
      ExprVector f;
      for (auto cst : csts) {
        Expr e = conv.toExpr(cst, m_efac);
        if (isOpX<FALSE>(e)) {
          f.clear();
          f.push_back(e);
        } else if (isOpX<TRUE>(e)) {
          continue;
        } else {
          f.push_back(e);
        }
      }
      out.insert(std::make_pair(b, f));
    }
  }

private:
  const LiveSymbols &m_ls;
  crab_llvm::HeapAbstraction &m_heap_abs;
  const Function &m_fn;
  ExprFactory &m_efac;
};
/** End convert from crab invariants to SeaHorn Expr **/

/*
   It builds a sliced Crab CFG wrt trace and performs abstract
   interpretation on it. This sliced CFG should correspond to a path
   in the original CFG.

   Return false iff the abstract interpretation of path is
   bottom. If bottom then it computes a blocking clause for that
   path.

   Modify m_active_bool_lits.

   NOTE: Currently, blocking clause is Boolean since the only
   abstraction we handle is Boolean.
 */
bool PathBasedBmcEngine::path_encoding_and_solve_with_ai(
    BmcTrace &trace, invariants_map_t &path_constraints) {
  using namespace crab_llvm;
  const Function &fun = *(this->m_fn);
  std::vector<const llvm::BasicBlock *> trace_blocks;

  LOG("bmc-details", errs() << "Trace=";);
  for (int i = 0; i < trace.size(); i++) {
    trace_blocks.push_back(trace.bb(i));
    LOG("bmc-details", errs() << trace.bb(i)->getName() << "  ";);
  }
  LOG("bmc-details", errs() << "\n";);

  // -- crab parameters
  AnalysisParams params;
  params.dom = CrabDom;
  
  // -- run crab on the path:
  //    If bottom is inferred then relevant_stmts is a minimal subset of
  //    statements along the path that still implies bottom.
  std::vector<crab::cfg::statement_wrapper> relevant_stmts;
  typename IntraCrabLlvm::invariant_map_t postmap, premap;
  const bool populate_constraints_map = true;
  bool res;
  if (populate_constraints_map) {
    // postmap contains the forward invariants
    // premap contains necessary preconditions
    res = m_crab_path->path_analyze(params, trace_blocks, LayeredCrabSolving,
                                    relevant_stmts, postmap, premap /*unused*/);

    // translate postmap (crab linear constraints) to path_constraints (Expr)
    crabToSea c2s(*m_ls, *(m_crab_global->get_heap_abstraction()), fun,
                  sem().efac());
    crab_path_map cm(postmap);
    c2s.convert(trace_blocks.begin(), trace_blocks.end(), cm, path_constraints);

  } else {
    res = m_crab_path->path_analyze(params, trace_blocks, LayeredCrabSolving,
                                    relevant_stmts);
  }

  if (!res) {
    LOG("bmc", get_os() << "Crab proved unsat.";
        // count the number of llvm instructions in the path
        unsigned num_stmts = 0;
        for (auto BB
             : trace_blocks) { num_stmts += BB->size(); } get_os()
        << " #Relevant statements " << relevant_stmts.size() << "/" << num_stmts
        << ".\n";);

    // Stats::resume ("BMC path-based: blocking clause");

    LOG("bmc-details", errs() << "\nRelevant Crab statements:\n";
        for (auto &s
             : relevant_stmts) {
          errs() << s.m_parent.get_name();
          if (s.m_parent.is_edge()) {
            auto e = s.m_parent.get_edge();
            errs() << " (" << e.first->getName() << "," << e.second->getName()
                   << ")";
          }
          errs() << ":\n";
          crab::outs() << "\t" << *(s.m_s) << "\n";
        });

    // -- Refine the Boolean abstraction from a minimal infeasible
    //    sequence of crab statements.
    /*
       1) A binary operation s at bb is translated to (bb => s)
       2) Most assignments are coming from PHI nodes:
          At bi, given "x = PHI (y, bj) (...)" crab translates it into x = y at
       bj. So we can translate it into ((bj and (bj and bi)) => x=y) 3)
       assume(cst) at bbi is coming from "f = ICMP cst at bb, BR f bbi, bbj",
       then we produce:
          ((bb and (bb and bbi)) => f)

       We need to take special care if an edge is critical:
        - a PHI node is translated into bj and tuple(bi,bj) => x=y
        - a branch is translated into b and tuple(bb,bbi) => f
    */

    std::set<Expr, lessExpr> active_bool_lits;
    for (auto it = relevant_stmts.begin(); it != relevant_stmts.end(); ++it) {
      crab::cfg::statement_wrapper s = *it;
      if (s.m_s->is_havoc()) {
        // The only reason a havoc statement is relevant is if we have something
        // like x:=*; assume(cond(x)); assert(cond(x)) Therefore, we can skip
        // it.
        continue;
      } else if ( // enumerate all statements here so that we can know if we
                  // miss one
          s.m_s->is_bin_op() || s.m_s->is_int_cast() || s.m_s->is_select() ||
          s.m_s->is_bool_bin_op() || s.m_s->is_bool_assign_cst() ||
          s.m_s->is_arr_write() || s.m_s->is_arr_read() || s.m_s->is_assume() ||
          s.m_s->is_bool_assume() ||
          // array initializations are not coming from branches
          s.m_s->is_arr_init() ||
          // array assignments are not coming from PHI nodes
          s.m_s->is_arr_assign()) {
        if (s.m_parent.is_edge()) {
          auto p = s.m_parent.get_edge();
          Expr src = sem().symb(*p.first);
          Expr dst = sem().symb(*p.second);

          Expr edge;
          if (isCriticalEdge(p.first, p.second)) {
            edge = bind::boolConst(mk<TUPLE>(src, dst));
            LOG("bmc-crab-blocking-clause",
                errs() << "Critical edge for branch between "
                       << p.first->getName() << " and " << p.second->getName()
                       << ":" << *edge << "\n";);
            active_bool_lits.insert(src);
          } else {
            edge = mk<AND>(src, dst);
            LOG("bmc-crab-blocking-clause",
                errs() << "Non-critical edge for branch between "
                       << p.first->getName() << " and " << p.second->getName()
                       << ":" << *edge << "\n";);
          }
          active_bool_lits.insert(edge);
        } else {
          const BasicBlock *BB = s.m_parent.get_basic_block();
          active_bool_lits.insert(sem().symb(*BB));
          LOG("bmc-crab-blocking-clause", errs()
                                              << "basic block " << BB->getName()
                                              << *(sem().symb(*BB)) << "\n";);
        }
        continue;
      } else if (s.m_s->is_assign() || s.m_s->is_bool_assign_var()) {
        const PHINode *Phi = nullptr;

        if (s.m_s->is_assign()) {
          typedef typename cfg_ref_t::basic_block_t::assign_t assign_t;
          auto assign = static_cast<const assign_t *>(s.m_s);
          if (boost::optional<const llvm::Value *> lhs =
                  assign->lhs().name().get()) {
            Phi = dyn_cast<PHINode>(*lhs);
          }
        } else {
          typedef typename cfg_ref_t::basic_block_t::bool_assign_var_t
              bool_assign_var_t;
          auto assign = static_cast<const bool_assign_var_t *>(s.m_s);
          if (boost::optional<const llvm::Value *> lhs =
                  assign->lhs().name().get()) {
            Phi = dyn_cast<PHINode>(*lhs);
          }
        }

        if (Phi) {
          const BasicBlock *src_BB = s.m_parent.get_basic_block();
          if (!src_BB) {
            src_BB = s.m_parent.get_edge().first;
            assert(src_BB);
          }
          const BasicBlock *dst_BB = Phi->getParent();
          Expr src = sem().symb(*src_BB);
          Expr dst = sem().symb(*dst_BB);
          Expr edge;
          if (isCriticalEdge(src_BB, dst_BB)) {
            edge = bind::boolConst(mk<TUPLE>(src, dst));
            LOG("bmc-crab-blocking-clause",
                errs() << "Critical edge for PHI Node between "
                       << src_BB->getName() << " and " << dst_BB->getName()
                       << ":" << *edge << "\n";);
            active_bool_lits.insert(src);
          } else {
            edge = mk<AND>(src, dst);
            LOG("bmc-crab-blocking-clause",
                errs() << "Non-critical edge for PHI Node between "
                       << src_BB->getName() << " and " << dst_BB->getName()
                       << ":" << *edge << "\n";);
          }
          active_bool_lits.insert(edge);
          continue;
        } else {
          // XXX assignment is not originated from a PHI node
          assert(!s.m_parent.is_edge());
          const BasicBlock *BB = s.m_parent.get_basic_block();
          assert(BB);
          active_bool_lits.insert(sem().symb(*BB));
          LOG("bmc-crab-blocking-clause",
              errs() << "basic block for assignment " << BB->getName()
                     << *(sem().symb(*BB)) << "\n";);
          continue;
        }
      }

      // sanity check: this should not happen.
      crab::outs() << "TODO: inference of active bool literals for " << *s.m_s
                   << "\n";
      // By returning true we pretend the query was sat so we run
      // the SMT solver next.
      // Stats::stop ("BMC path-based: blocking clause");
      return true;
    } // end for

    // -- Finally, evaluate the symbolic boolean variables in their
    //    corresponding symbolic stores.

    // Symbolic states are associated with cutpoints
    m_active_bool_lits.clear();
    auto &cps = getCps();
    std::vector<SymStore> &states = getStates();
    for (Expr e : active_bool_lits) {
      // Find the state where e is defined.
      // XXX: this is expensive but don't know how to do it better.
      bool found = false;
      for (unsigned i = 0; i < cps.size(); ++i) {
        const CutPoint *cp = cps[i];
        SymStore &s = states[i];
        Expr v = s.eval(e);
        if (v != e) {
          m_active_bool_lits.push_back(v);
          found = true;
          break;
        }
        if (isTuple(e)) {
          // s.eval does not traverse function declarations
          auto t = getTuple(e);
          if (s.isDefined(t.first) && s.isDefined(t.second)) {
            m_active_bool_lits.push_back(
                bind::boolConst(mk<TUPLE>(s.eval(t.first), s.eval(t.second))));
            found = true;
            break;
          }
        }
      }

      if (!found) {
        // Sanity check
        errs()
            << "Path-based BMC ERROR: cannot produce an unsat core from Crab\n";
        // XXX: we continue and pretend the query was satisfiable so
        // nothing really happens and the smt solver is used next.
        return true;
      }
    }

    /////////////////////////
    //// DEBUGGING
    // Expr crab_bc = op::boolop::lneg(op::boolop::land(m_active_bool_lits));
    // llvm::errs() << "Blocking clause using crab: " << *crab_bc << "\n";
    // m_active_bool_lits.clear();
    // return true;
    /////////////////////////
  }
  return res;
}
#endif

/*
  First, it builds an implicant of the precise encoding (m_side)
  with respect to the model. This implicant should correspond to a
  path. Then, it checks that the implicant is unsatisfiable. If yes,
  it produces a blocking clause for that path. Otherwise, it
  produces a model.

  Modify: m_aux_smt_solver, m_active_bool_lits, and m_model.

  NOTE: Currently, blocking clauses are Boolean since the only
  abstraction we handle is Boolean.
*/
boost::tribool PathBasedBmcEngine::path_encoding_and_solve_with_smt(
    ufo::ZModel<ufo::EZ3> &model, const invariants_map_t & /*invariants*/,
    // extra constraints inferred by
    // crab for current implicant
    const invariants_map_t & /*path_constraints*/) {

  ExprVector path_formula, assumptions;
  path_formula.reserve(m_side.size());

  // make a copy of m_side since get_model_implicant modifies it.
  ExprVector f(m_side.begin(), m_side.end());

  ExprMap active_bool_map;

  // TODO: BmcTrace already computed the implicant so we might
  // compute the implicant twice if crab is enabled.
  bmc_impl::get_model_implicant(f, model, path_formula, active_bool_map);

#if 0
    // remove redundant literals
    // XXX: possibly cause of non-determinism?
    std::sort(path_formula.begin(), path_formula.end());
    path_formula.erase(std::unique(path_formula.begin(), path_formula.end()),
		       path_formula.end());
#endif

  LOG("bmc-details", errs() << "PATH FORMULA:\n";
      for (Expr e
           : path_formula) { errs() << "\t" << *e << "\n"; });

  // For debugging
  // if (SmtOutDir != "") {
  //   toSmtLib(path_formula);
  // }

  /*****************************************************************
   * This check might be expensive if path_formula contains complex
   * bitvector/floating point expressions.
   * TODO: make decisions `a la` mcsat to solve faster. We will use
   * here invariants to make only those decisions which are
   * consistent with the invariants.
   *****************************************************************/
  m_aux_smt_solver.reset();
  // TODO: add here path_constraints to help
  for (Expr e : path_formula) {
    m_aux_smt_solver.assertExpr(e);
  }

  boost::tribool res;
  {
    scoped_solver ss(m_aux_smt_solver, PathTimeout);
    res = ss.get().solve();
  }
  if (res) {
    m_model = m_aux_smt_solver.getModel();
    if (SmtOutDir != "") {
      toSmtLib(path_formula, "sat");
    }
  } else {
    // Stats::resume ("BMC path-based: SMT unsat core");
    // --- Compute minimal unsat core of the path formula
    bmc_detail::muc_method_t muc_method = MucMethod;
    if (!res) {
      LOG("bmc", get_os() << "SMT proved unsat. Size of path formula="
                          << path_formula.size() << ". ");
    } else {
      muc_method = bmc_detail::MUC_NONE;
      res = false;
      m_incomplete = true;
      LOG("bmc", get_os() << "SMT returned unknown. Size of path formula="
                          << path_formula.size() << ". ");

      Stats::count("BMC total number of unknown symbolic paths");

      // -- Enqueue the unknown path formula
      m_unknown_path_formulas.push(std::make_pair(m_num_paths, path_formula));

      if (SmtOutDir != "") {
        toSmtLib(path_formula, "unknown");
      }
    }

    ExprVector unsat_core;
    switch (muc_method) {
    case bmc_detail::MUC_NONE: {
      unsat_core.assign(path_formula.begin(), path_formula.end());
      break;
    }
    case bmc_detail::MUC_DELETION: {
      deletion_muc muc(m_aux_smt_solver);
      muc.run(path_formula, unsat_core);
      LOG("bmc-unsat-core", errs() << "\n"; muc.print_stats(errs()));
      break;
    }
    case bmc_detail::MUC_BINARY_SEARCH: {
      binary_search_muc muc(m_aux_smt_solver);
      muc.run(path_formula, unsat_core);
      LOG("bmc-unsat-core", errs() << "\n"; muc.print_stats(errs()));
      break;
    }
    case bmc_detail::MUC_ASSUMPTIONS:
    default: {
      muc_with_assumptions muc(m_aux_smt_solver);
      muc.run(path_formula, unsat_core);
      LOG("bmc-unsat-core", errs() << "\n"; muc.print_stats(errs()));
      break;
    }
    }
    // Stats::stop ("BMC path-based: SMT unsat core");

    LOG("bmc", get_os() << "Size of unsat core=" << unsat_core.size() << "\n";
        // errs() << "unsat core=\n";
        // for (auto e: unsat_core) {
        //   errs () << *e << "\n";
        // }
    );

    // Stats::resume ("BMC path-based: blocking clause");
    // -- Refine the Boolean abstraction using the unsat core
    ExprSet active_bool_set;
    for (Expr e : unsat_core) {
      auto it = active_bool_map.find(e);
      // It's possible that an implicant has no active booleans.
      // For instance, corner cases where the whole program is a
      // single block.
      if (it != active_bool_map.end()) {
        active_bool_set.insert(it->second);
      }
    }
    m_active_bool_lits.assign(active_bool_set.begin(), active_bool_set.end());
    // Stats::stop ("BMC path-based: blocking clause");
  }

  return res;
}

#ifdef HAVE_CRAB_LLVM
PathBasedBmcEngine::PathBasedBmcEngine(LegacyOperationalSemantics &sem,
                                       ufo::EZ3 &zctx,
                                       crab_llvm::CrabLlvmPass *crab,
                                       const TargetLibraryInfo &tli)
    : BmcEngine(sem, zctx), m_incomplete(false), m_num_paths(0),
      m_aux_smt_solver(zctx), m_tli(tli), m_model(zctx), m_ls(nullptr),
      m_crab_global(crab), m_crab_path(nullptr) {}
#else
PathBasedBmcEngine::PathBasedBmcEngine(LegacyOperationalSemantics &sem,
                                       ufo::EZ3 &zctx,
                                       const TargetLibraryInfo &tli)
    : BmcEngine(sem, zctx), m_incomplete(false), m_num_paths(0),
      m_aux_smt_solver(zctx), m_tli(tli), m_model(zctx), m_ls(nullptr) {}
#endif

PathBasedBmcEngine::~PathBasedBmcEngine() {
  if (m_ls)
    delete m_ls;
#ifdef HAVE_CRAB_LLVM
  if (m_crab_path)
    delete m_crab_path;
#endif
}

// Print a path to a SMT-LIB file (for debugging purposes)
void PathBasedBmcEngine::toSmtLib(const ExprVector &f, std::string prefix) {
  assert(SmtOutDir != "");

  std::error_code EC;
  std::string DirName = SmtOutDir;

  // get absolute path to the directory
  SmallVector<char, 256> path;
  EC = sys::fs::make_absolute(DirName, path);
  if (EC) {
    errs() << "Cannot find absolute path to " << DirName << "\n";
    return;
  }
  // create the directory
  EC = sys::fs::create_directory(path, true /*ignore if dir exists*/);
  if (EC) {
    errs() << "Cannot create directory " << DirName << "\n";
    return;
  }
  // create a file name
  std::string Filename("path_" + prefix + "_" + std::to_string(m_num_paths));
  {
    time_t now = time(0);
    struct tm tstruct;
    char buf[80];
    tstruct = *localtime(&now);
    strftime(buf, sizeof(buf), "__%Y-%m-%d.%H-%M-%S", &tstruct);
    std::string suffix(buf);
    Filename = Filename + "_" + suffix;
  }
  Filename = Filename + ".smt2";
  sys::path::append(path, Filename);
  Twine fullFilename(path);

  // create a file descriptor
  raw_fd_ostream fd(fullFilename.toStringRef(path), EC, sys::fs::F_Text);
  if (EC) {
    errs() << "Could not open: " << Filename << "\n";
    return;
  }

  // dump the formula to the file descriptor
  m_aux_smt_solver.reset();
  for (Expr e : f) {
    m_aux_smt_solver.assertExpr(e);
  }
  m_aux_smt_solver.toSmtLib(fd);
  m_aux_smt_solver.reset();
}

raw_ostream &PathBasedBmcEngine::toSmtLib(raw_ostream &o) {
  encode(false);

  m_aux_smt_solver.reset();
  for (Expr e : m_side) {
    m_aux_smt_solver.assertExpr(e);
  }
  m_aux_smt_solver.toSmtLib(o);
  m_aux_smt_solver.reset();
  return o;
}

void PathBasedBmcEngine::encode(bool assert_formula /*unused*/) {
  /** Note that we never assert the encoding into the solver **/

  Stats::resume("BMC path-based: precise encoding");
  BmcEngine::encode(/*assert_formula=*/false);
  Stats::stop("BMC path-based: precise encoding");
}

static inline boost::tribool path_solver(ufo::ZSolver<ufo::EZ3> &solver) {
  Stats::resume("BMC path-based: path solver");
  boost::tribool res = solver.solve();
  Stats::stop("BMC path-based: path solver");
  return res;
}

boost::tribool PathBasedBmcEngine::solve() {
  LOG("bmc", get_os(true) << "Starting path-based BMC \n";);

  // -- Precise encoding
  LOG("bmc", get_os(true) << "Begin precise encoding\n";);
  encode(/*assert_formula=*/false);
  LOG("bmc", get_os(true) << "End precise encoding\n";);

  LOG("bmc-details", errs() << "Begin precise encoding:\n";
      for (Expr v
           : m_side) errs()
      << "\t" << *v << "\n";
      errs() << "End precise encoding\n";);

  // -- Boolean abstraction
  LOG("bmc", get_os(true) << "Begin boolean abstraction\n";);
  Stats::resume("BMC path-based: initial boolean abstraction");
  ExprVector abs_side;
  bool_abstraction(m_side, abs_side);
  // XXX: we use m_smt_solver for keeping the abstraction. We do
  //      that so that BmcTrace access to the right solver.
  for (Expr v : abs_side) {
    LOG("bmc-details", errs() << "\t" << *v << "\n";);
    m_smt_solver.assertExpr(v);
  }
  Stats::stop("BMC path-based: initial boolean abstraction");
  LOG("bmc", get_os(true) << "End boolean abstraction\n";);

  // -- Numerical abstraction
  invariants_map_t invariants;
#ifdef HAVE_CRAB_LLVM
  // Convert crab invariants to Expr
  if (UseCrab && m_crab_global) {

    // -- Compute live symbols so that invariant variables exclude
    //    dead variables.
    m_ls = new LiveSymbols(*m_fn, sem().efac(), sem());
    m_ls->run();

    if (UseCrabGlobalInvariants) {
      LOG("bmc", get_os(true) << "Begin loading of crab global invariants\n";);
      Stats::resume("BMC path-based: loading of crab global invariants");

      // -- Translate invariants
      crabToSea c2s(*m_ls, *(m_crab_global->get_heap_abstraction()), *m_fn,
                    sem().efac());
      crab_global_map cm(*m_crab_global);
      // convert references to pointers (FIXME: use make_transform_iterator)
      std::vector<const BasicBlock *> bb_ptr_vector;
      bb_ptr_vector.reserve(m_fn->size());
      for (const BasicBlock &b : *m_fn) {
        bb_ptr_vector.push_back(&b);
      }
      c2s.convert(bb_ptr_vector.begin(), bb_ptr_vector.end(), cm, invariants);

      LOG("bmc-ai", for (auto &kv
                         : invariants) {
        errs() << "Global invariants at " << kv.first->getName() << ": ";
        if (kv.second.empty()) {
          errs() << "true\n";
        } else {
          errs() << "\n";
          for (auto e : kv.second) {
            errs() << "\t" << *e << "\n";
          }
        }
      });

      // -- Load the numerical abstraction (invariants) into the solver
      for (auto &kv : invariants) {
        const BasicBlock *bb = kv.first;
        ExprVector inv = kv.second;
        if (inv.empty())
          continue;
        Expr bbV = sem().symb(*bb);
        m_smt_solver.assertExpr(mk<IMPL>(bbV, op::boolop::land(inv)));
      }
      Stats::stop("BMC path-based: loading of crab global invariants");
      LOG("bmc", get_os(true) << "End loading of crab invariants\n";);
    }
  }
#endif

#ifdef HAVE_CRAB_LLVM
  crab_llvm::CfgManager cfg_man;
  if (UseCrab && m_crab_global) {
    /**
       Create another instance of crab to analyze single paths
       TODO: make these options user options
    **/
    const crab::cfg::tracked_precision prec_level = crab::cfg::ARR;
    auto heap_abstraction = m_crab_global->get_heap_abstraction();
    // TODO: modify IntraCrabLlvm api so that it takes the cfg already
    // generated by m_crab_global
    m_crab_path = new crab_llvm::IntraCrabLlvm(
        *(const_cast<Function *>(this->m_fn)), m_tli, cfg_man, prec_level,
        heap_abstraction);
    LOG("bmc", if (UseCrab) {
      get_os() << "Processing symbolic paths\n";
      switch (CrabDom) {
      case crab_llvm::TERMS_INTERVALS:
        get_os() << "Using term+interval domain for solving paths\n";
        break;
      case crab_llvm::WRAPPED_INTERVALS:
        get_os() << "Using wrapped interval domain for solving paths\n";
        break;
      case crab_llvm::TERMS_ZONES:
        get_os() << "Using terms+zones domain for solving paths\n";
        break;
      case crab_llvm::ZONES_SPLIT_DBM:
        get_os() << "Using zones domain for solving paths\n";
        break;
      default:
        get_os() << "Using interval domain for solving paths\n";
      }
    });
  }
#endif

  /**
   * Main loop
   *
   * Use boolean abstraction to enumerate paths. Each time a path is
   * unsat, blocking clauses are added to avoid exploring the same
   * path.
   **/
  while ((bool)(m_result = path_solver(m_smt_solver))) {
    ++m_num_paths;
    Stats::count("BMC total number of symbolic paths");

    LOG("bmc", get_os(true) << m_num_paths << ": ");
    Stats::resume("BMC path-based: get model");
    ufo::ZModel<ufo::EZ3> model = m_smt_solver.getModel();
    Stats::stop("BMC path-based: get model");

    LOG("bmc-details", errs() << "Model " << m_num_paths << " found: \n"
                              << model << "\n";);

    invariants_map_t path_constraints;
#ifdef HAVE_CRAB_LLVM
    if (UseCrab && m_crab_global) {
      BmcTrace trace(*this, model);
      Stats::resume("BMC path-based: solving path + learning clauses with AI");
      bool res = path_encoding_and_solve_with_ai(trace, path_constraints);
      Stats::stop("BMC path-based: solving path + learning clauses with AI");

      LOG("bmc-ai",
          errs() << "\nPath constraints (post-conditions) inferred by AI\n";
          for (auto &kv
               : path_constraints) {
            errs() << "\t" << kv.first->getName() << ": ";
            if (kv.second.empty()) {
              errs() << "true\n";
            } else {
              errs() << "{";
              for (auto e : kv.second) {
                errs() << *e << ";";
              }
              errs() << "}\n";
            }
          });

      if (!res) {
        bool ok = add_blocking_clauses();
        if (ok) {
          Stats::count("BMC number symbolic paths discharged by AI");
          continue;
        } else {
          errs() << "Path-based BMC ERROR: same blocking clause again "
                 << __LINE__ << "\n";
          m_result = boost::indeterminate;
          return m_result;
        }
      }
    }
#endif
    Stats::resume("BMC path-based: solving path + learning clauses with SMT");
    boost::tribool res =
        path_encoding_and_solve_with_smt(model, invariants, path_constraints);
    Stats::stop("BMC path-based: solving path + learning clauses with SMT");
    if (res) {
#ifdef HAVE_CRAB_LLVM
      if (UseCrab) {
	// Temporary: for profiling crab
	crab::CrabStats::PrintBrunch(crab::outs());
      }
#endif
      m_result = res;
      return res;
    } else {
      // if res is unknown we still add a blocking clause to skip
      // the path.
      bool ok = add_blocking_clauses();
      if (!ok) {
        errs() << "Path-based BMC ERROR: same blocking clause again "
               << __LINE__ << "\n";
        m_result = boost::indeterminate;
        return m_result;
      }
      Stats::count("BMC number symbolic paths discharged by SMT");
    }
  }

  if (m_incomplete) {
    m_result = indeterminate;

    LOG("bmc",
        get_os()
            << "Checking again unsolved paths with increasing timeout ...\n");
    // XXX: can be user parameter
    const unsigned timeout_delta = 10; // (seconds)
    boost::unordered_map<unsigned, unsigned> timeout_map;
    while (!m_unknown_path_formulas.empty()) {
      auto kv = m_unknown_path_formulas.front();
      m_unknown_path_formulas.pop();

      m_aux_smt_solver.reset();
      for (Expr e : kv.second) {
        m_aux_smt_solver.assertExpr(e);
      }

      unsigned timeout;
      auto it = timeout_map.find(kv.first);
      if (it == timeout_map.end()) {
        timeout_map.insert(
            std::make_pair(kv.first, PathTimeout + timeout_delta));
        timeout = PathTimeout + timeout_delta;
      } else {
        timeout = it->second + timeout_delta;
        it->second = timeout;
      }

      boost::tribool res;
      {
        scoped_solver ss(m_aux_smt_solver, timeout);
        res = ss.get().solve();
      }
      if (res) {
        m_model = m_aux_smt_solver.getModel();
        if (SmtOutDir != "") {
          toSmtLib(kv.second, "sat");
        }
        LOG("bmc", get_os(true) << "Path " << kv.first << " proved sat!\n";);
        m_result = (bool)true;
        return m_result;
      } else if (!res) {
        LOG("bmc", get_os(true) << "Path " << kv.first << " proved unsat!\n";);
      } else {
        LOG("bmc", get_os(true) << "Path " << kv.first
                                << " cannot be proved unsat with timeout="
                                << timeout << "\n";);
        // put it back in the queue and try next time with a bigger timeout
        m_unknown_path_formulas.push(kv);
      }
    }
    // If we reach this point we were able to discharge all the paths!
    Stats::uset("BMC total number of unknown symbolic paths", 0);
    m_result = (bool)false;
  }

  if (m_num_paths == 0) {
    errs() << "\nProgram is trivially unsat: initial boolean abstraction was "
              "enough.\n";
  }

#ifdef HAVE_CRAB_LLVM
  if (UseCrab) {
    // Temporary: for profiling crab    
    crab::CrabStats::PrintBrunch(crab::outs());
  }
#endif

  return m_result;
}

bool PathBasedBmcEngine::add_blocking_clauses() {
  Stats::resume("BMC path-based: adding blocking clauses");

  // -- Refine the Boolean abstraction
  Expr bc = mk<FALSE>(sem().efac());
  if (m_active_bool_lits.empty()) {
    errs() << "No found active boolean literals. Trivially unsat ... \n";
  } else {
    bc = op::boolop::lneg(op::boolop::land(m_active_bool_lits));
  }
  LOG("bmc-details",
      errs() << "Added blocking clause to refine Boolean abstraction: " << *bc
             << "\n";);

  m_smt_solver.assertExpr(bc);
  auto res = m_blocking_clauses.insert(bc);
  bool ok = res.second;

  Stats::stop("BMC path-based: adding blocking clauses");
  return ok;
}

BmcTrace PathBasedBmcEngine::getTrace() {
  assert((bool)m_result);
  BmcTrace trace(*this, m_model);
  return trace;
}

ufo::ZModel<ufo::EZ3> PathBasedBmcEngine::getModel() {
  assert((bool)m_result);
  return m_model;
}

// This is intending only for debugging purposes
void PathBasedBmcEngine::unsatCore(ExprVector &out) {
  // TODO: for path-based BMC is not clear what to return.
}

} // namespace seahorn
