#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/BitwuzlaEncodingCheck.hh"
#include "seahorn/Expr/Smt/BitwuzlaModelImpl.hh"
#include "seahorn/Expr/Smt/BitwuzlaSmtLib.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <limits>
#include <unistd.h>
#include <unordered_set>
#include <utility>
#include <vector>

using namespace expr;
using bitwuzla::Option;

static llvm::cl::opt<std::string> CheckEncodingLog(
    "horn-bw-check-encoding",
    llvm::cl::desc("For every formula given to Bitwuzla, have Z3 check that it "
                   "means the same as Z3's encoding, and append the verdict "
                   "to this file (slow; for testing)"),
    llvm::cl::value_desc("file"), llvm::cl::init(""), llvm::cl::Hidden);

static llvm::cl::opt<unsigned> CheckEncodingTimeout(
    "horn-bw-check-encoding-timeout",
    llvm::cl::desc("Z3 time limit for each check of --horn-bw-check-encoding"),
    llvm::cl::value_desc("ms"), llvm::cl::init(10000), llvm::cl::Hidden);

namespace seahorn {
namespace solver {

/// Appends one line to the --horn-bw-check-encoding file: the verdict, the
/// time it took, the process, and the detail
static void logEncodingCheck(const std::string &verdict, long ms,
                             std::string detail) {
  for (char &ch : detail)
    if (ch == '\n' || ch == '\t')
      ch = ' ';
  std::ofstream log(CheckEncodingLog, std::ios::app);
  log << verdict << "\t" << ms << "ms\tpid " << ::getpid() << "\t" << detail
      << "\n";
}

/// Translation validation of one formula, when --horn-bw-check-encoding is on
static void checkEncoding(Expr exp, const bitwuzla::Term &t,
                          bitwuzla::TermManager *tm) {
  auto start = std::chrono::steady_clock::now();
  EncodingCheck res = checkBitwuzlaEncoding(exp, t, CheckEncodingTimeout, tm);
  long ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start)
                .count();
  if (res.verdict == EncodingVerdict::DIFFERENT)
    ERR << "Bitwuzla's formula differs from Z3's encoding: " << res.detail;
  logEncodingCheck(verdictName(res.verdict), ms, res.detail);
}

static std::unique_ptr<bitwuzla::Bitwuzla>
mkBitwuzla(bitwuzla::TermManager &tm, const bitwuzla::Options &options) {
  try {
    return std::make_unique<bitwuzla::Bitwuzla>(tm, options);
  } catch (std::exception &ex) {
    llvm::report_fatal_error(
        llvm::StringRef(std::string("cannot create Bitwuzla: ") + ex.what()));
  }
}

// -- Bitwuzla 0.9.1 can give an equality between arrays a wrong model value.
// -- It compares the two arrays' value terms for identity
// -- (rewrite/evaluator.cpp:28). Values are canonical (one store per index
// -- that an access touches, none equal to the default:
// -- ArraySolver::construct_model_value), so that is wrong only for two
// -- different defaults whose stores together write every index. It happens
// -- for an equality outside the assertions, and for one in the assertions
// -- that preprocessing moved into a constant's definition (with q = (a = b)
// -- asserted, q's value is that comparison).

/// Arrays with indices at least this wide are safe from it: one of the two
/// values would need 2^31 stores, so the formula 2^31 accesses
static const uint64_t WIDE_INDEX = 32;

// -- The two searches below skip the terms of a set known to have nothing
// -- they look for inside. A search that finds nothing adds what it visited
// -- to the set. One that finds something stops early, so some terms it
// -- visited were not searched to the end: they are not added. So the set
// -- stays true when a pop() removes the assertion that was found.

/// \p t has an equality or disequality between arrays whose index is
/// narrower than \p width bits. \p clean holds terms known to have none.
static bool hasArrayEquality(const bitwuzla::Term &t,
                             std::unordered_set<bitwuzla::Term> &clean,
                             uint64_t width) {
  std::unordered_set<bitwuzla::Term> seen;
  std::vector<bitwuzla::Term> todo{t};
  while (!todo.empty()) {
    bitwuzla::Term u = todo.back();
    todo.pop_back();
    if (clean.count(u) || !seen.insert(u).second)
      continue;
    if ((u.kind() == bitwuzla::Kind::EQUAL ||
         u.kind() == bitwuzla::Kind::DISTINCT) &&
        u[0].sort().is_array()) {
      bitwuzla::Sort index = u[0].sort().array_index();
      if (!index.is_bv() || index.bv_size() < width)
        return true;
    }
    for (const bitwuzla::Term &ch : u.children())
      todo.push_back(ch);
  }
  clean.insert(seen.begin(), seen.end());
  return false;
}

// -- Bitwuzla 0.9.1 gives a forall in the assertions the value of its
// -- abstraction, and for one outside them (one that preprocessing moved
// -- into a constant's definition, or one in a term asked for) get_value
// -- registers it and solves again (solver_engine.cpp:236-264, 500-507). So
// -- values of a formula with quantifiers might come from different models.

/// \p t has a forall or an exists. \p clean holds terms known to have none.
static bool hasQuantifier(const bitwuzla::Term &t,
                          std::unordered_set<bitwuzla::Term> &clean) {
  std::unordered_set<bitwuzla::Term> seen;
  std::vector<bitwuzla::Term> todo{t};
  while (!todo.empty()) {
    bitwuzla::Term u = todo.back();
    todo.pop_back();
    if (clean.count(u) || !seen.insert(u).second)
      continue;
    if (u.kind() == bitwuzla::Kind::FORALL ||
        u.kind() == bitwuzla::Kind::EXISTS)
      return true;
    for (const bitwuzla::Term &ch : u.children())
      todo.push_back(ch);
  }
  clean.insert(seen.begin(), seen.end());
  return false;
}

/// \p s on one line, for an SMT-LIB comment
static std::string oneLine(std::string s) {
  std::replace(s.begin(), s.end(), '\n', ' ');
  std::replace(s.begin(), s.end(), '\r', ' ');
  return s;
}

bitwuzla_solver_impl::bitwuzla_solver_impl(uint64_t time_limit_ms)
    : Solver(), m_marshal(m_tm),
      m_self(std::make_shared<bitwuzla_solver_impl *>(this)) {
  // -- options must be set before the Bitwuzla instance is created. Not
  // -- PRODUCE_UNSAT_ASSUMPTIONS: see enableCores()
  m_options.set(Option::PRODUCE_MODELS, true);
  if (time_limit_ms != 0)
    m_options.set(Option::TIME_LIMIT_PER, time_limit_ms);
  m_bzla = mkBitwuzla(m_tm, m_options);
}

bitwuzla_solver_impl::~bitwuzla_solver_impl() = default;

void bitwuzla_solver_impl::guard(const bitwuzla::Term &t, bool assumed) {
  bool &narrow = assumed ? m_assumed_narrow_array_eq : m_narrow_array_eq;
  bool &quantified = assumed ? m_assumed_quantified : m_quantified;
  const char *what = assumed ? "an assumption" : "an assertion";
  if (!narrow && hasArrayEquality(t, m_no_array_eq, WIDE_INDEX)) {
    narrow = true;
    LOG("bitwuzla", WARN << what
                         << " has an equality between arrays with narrow "
                            "indices, so models have no values";);
  }
  if (!quantified && hasQuantifier(t, m_no_quantifier)) {
    quantified = true;
    LOG("bitwuzla",
        WARN << what << " has a quantifier, so models have no values";);
  }
}

bool bitwuzla_solver_impl::add(Expr exp) {
  changed();
  try {
    bitwuzla::Term t = m_marshal.encode_term(exp);
    if (!CheckEncodingLog.empty())
      checkEncoding(exp, t, &m_tm);
    m_bzla->assert_formula(t);
    m_assertions.push_back(exp);
    m_terms.push_back(t);
    guard(t, false);
    return true;
  } catch (std::exception &ex) {
    if (!CheckEncodingLog.empty())
      logEncodingCheck("NOT-ENCODED", 0, ex.what());
    // -- UnsupportedExpr, or a bitwuzla::Exception such as for an assertion
    // -- that is not Boolean. Keep the first reason.
    if (m_unsupported.empty()) {
      m_unsupported = ex.what();
      WARN << "Bitwuzla cannot encode an assertion, so checks answer "
              "unknown: "
           << m_unsupported;
    }
  }
  return false;
}

SolverResult
bitwuzla_solver_impl::solve(const std::vector<bitwuzla::Term> &assumptions) {
  if (!m_lost.empty()) {
    LOG("bitwuzla", WARN << "answering unknown: " << m_lost;);
    return SolverResult::UNKNOWN;
  }
  if (!m_unsupported.empty()) {
    LOG("bitwuzla", WARN << "answering unknown: " << m_unsupported;);
    return SolverResult::UNKNOWN;
  }
  try {
    switch (m_bzla->check_sat(assumptions)) {
    case bitwuzla::Result::SAT:
      m_sat_generation = m_generation;
      return SolverResult::SAT;
    case bitwuzla::Result::UNSAT:
      m_unsat_generation = m_generation;
      return SolverResult::UNSAT;
    case bitwuzla::Result::UNKNOWN:
      return SolverResult::UNKNOWN;
    }
  } catch (std::exception &ex) {
    ERR << "Bitwuzla check failed: " << ex.what();
  }
  return SolverResult::ERROR;
}

SolverResult bitwuzla_solver_impl::check() {
  changed();
  m_assumptions.clear();
  m_assumed_narrow_array_eq = false;
  m_assumed_quantified = false;
  return solve({});
}

std::vector<size_t> bitwuzla_solver_impl::levels() const {
  std::vector<size_t> out;
  size_t level = 0;
  for (size_t i = 0, n = m_terms.size(); i < n; ++i) {
    while (level < m_scopes.size() && m_scopes[level].num_assertions <= i)
      ++level;
    out.push_back(level);
  }
  return out;
}

// -- Without PRODUCE_UNSAT_ASSUMPTIONS, Bitwuzla checks under assumptions
// -- but cannot say which were unsat (probe18a). The option turns on
// -- PRODUCE_UNSAT_CORES (option.cpp:829-834), which changes preprocessing
// -- (variable substitution, skeleton preprocessing, embedded constraints)
// -- and tracks every assertion in the bit-blaster; a check that answered
// -- sat answered unknown with it (bitwuzla.model after an equality of
// -- narrow arrays). So it is turned on only by the first assumption check:
// -- a new instance gets the assertions again, in their scopes. Mono BMC
// -- never checks under assumptions. reset() turns it off again (Path BMC
// -- checks paths plainly between its cores; review of step 1.8).
void bitwuzla_solver_impl::enableCores() {
  if (m_cores)
    return;
  m_cores = true;
  m_options.set(Option::PRODUCE_UNSAT_ASSUMPTIONS, true);
  try {
    std::unique_ptr<bitwuzla::Bitwuzla> fresh = mkBitwuzla(m_tm, m_options);
    std::vector<size_t> lv = levels();
    size_t level = 0;
    for (size_t i = 0, n = m_terms.size(); i < n; ++i) {
      for (; level < lv[i]; ++level)
        fresh->push(1);
      fresh->assert_formula(m_terms[i]);
    }
    for (; level < m_scopes.size(); ++level)
      fresh->push(1);
    m_bzla = std::move(fresh);
  } catch (std::exception &ex) {
    ERR << "Bitwuzla adapter: cannot turn on unsat assumptions: " << ex.what();
    if (m_lost.empty())
      m_lost = std::string("turning on unsat assumptions failed: ") + ex.what();
  }
}

SolverResult
bitwuzla_solver_impl::check_with_assumptions(const expr_const_it_range &lits) {
  changed();
  enableCores();
  m_assumptions.clear();
  m_assumed_narrow_array_eq = false;
  m_assumed_quantified = false;
  std::vector<bitwuzla::Term> terms;
  try {
    ExprSet given;
    for (Expr a : lits) {
      if (!given.insert(a).second)
        continue;
      bitwuzla::Term t = m_marshal.encode_term(a);
      // -- Bitwuzla 0.9.1 takes a bit-vector as an assumption, and answers
      // -- (probe18a)
      if (!t.sort().is_bool()) {
        WARN << "Bitwuzla adapter: an assumption of sort " << t.sort().str()
             << " is not Bool, so this check answers unknown";
        m_assumptions.clear();
        return SolverResult::UNKNOWN;
      }
      if (!CheckEncodingLog.empty())
        checkEncoding(a, t, &m_tm);
      m_assumptions.push_back({t, a});
      terms.push_back(t);
      guard(t, true);
    }
  } catch (std::exception &ex) {
    // -- UnsupportedExpr, or a bitwuzla::Exception
    if (!CheckEncodingLog.empty())
      logEncodingCheck("NOT-ENCODED", 0, ex.what());
    WARN << "Bitwuzla cannot encode an assumption, so this check answers "
            "unknown: "
         << ex.what();
    m_assumptions.clear();
    return SolverResult::UNKNOWN;
  }
  return solve(terms);
}

void bitwuzla_solver_impl::unsat_core(ExprVector &out) {
  if (m_unsat_generation != m_generation) {
    ERR << "Bitwuzla adapter: unsat_core needs the last check to be unsat, "
           "with no change since; no core";
    return;
  }
  // -- after check(), or with no assumptions: the assertions alone are unsat
  if (m_assumptions.empty())
    return;
  try {
    std::vector<bitwuzla::Term> unsat = m_bzla->get_unsat_assumptions();
    std::unordered_set<bitwuzla::Term> core(unsat.begin(), unsat.end());
    std::unordered_set<bitwuzla::Term> ours;
    for (auto &ta : m_assumptions)
      ours.insert(ta.first);
    bool known =
        std::all_of(core.begin(), core.end(), [&](const bitwuzla::Term &t) {
          return ours.count(t) != 0;
        });
    if (known) {
      for (auto &ta : m_assumptions)
        if (core.count(ta.first))
          out.push_back(ta.second);
      return;
    }
    ERR << "Bitwuzla adapter: Bitwuzla named an unsat assumption that was "
           "not given; the core is every assumption";
  } catch (std::exception &ex) {
    ERR << "Bitwuzla adapter: no unsat assumptions from Bitwuzla (" << ex.what()
        << "); the core is every assumption";
  }
  // -- the check was unsat, so all the assumptions are a core
  for (auto &ta : m_assumptions)
    out.push_back(ta.second);
}

void bitwuzla_solver_impl::push() {
  changed();
  try {
    m_bzla->push(1);
  } catch (std::exception &ex) {
    ERR << "Bitwuzla adapter: push failed: " << ex.what();
    if (m_lost.empty())
      m_lost = std::string("a push failed: ") + ex.what();
    return;
  }
  m_scopes.push_back(
      {m_assertions.size(), m_unsupported, m_narrow_array_eq, m_quantified});
}

void bitwuzla_solver_impl::pop() {
  changed();
  if (m_scopes.empty()) {
    ERR << "Bitwuzla adapter: pop without a push; checks answer unknown "
           "until reset";
    if (m_lost.empty())
      m_lost = "pop without a push";
    return;
  }
  Scope s = m_scopes.back();
  m_scopes.pop_back();
  try {
    m_bzla->pop(1);
  } catch (std::exception &ex) {
    ERR << "Bitwuzla adapter: pop failed: " << ex.what();
    if (m_lost.empty())
      m_lost = std::string("a pop failed: ") + ex.what();
    return;
  }
  m_assertions.resize(s.num_assertions);
  m_terms.resize(s.num_assertions);
  m_unsupported = s.unsupported;
  m_narrow_array_eq = s.narrow_array_eq;
  m_quantified = s.quantified;
}

void bitwuzla_solver_impl::reset() {
  changed();
  // -- a fresh instance, without unsat assumptions; the TermManager and the
  // -- encoder's cache stay valid
  m_cores = false;
  m_options.set(Option::PRODUCE_UNSAT_ASSUMPTIONS, false);
  m_bzla.reset();
  m_bzla = mkBitwuzla(m_tm, m_options);
  m_unsupported.clear();
  m_lost.clear();
  m_assertions.clear();
  m_terms.clear();
  m_scopes.clear();
  m_narrow_array_eq = false;
  m_quantified = false;
  // -- (still true, but they would keep every term ever seen alive)
  m_no_array_eq.clear();
  m_no_quantifier.clear();
  m_assumptions.clear();
  m_assumed_narrow_array_eq = false;
  m_assumed_quantified = false;
}

bitwuzla_solver_impl::model_ref bitwuzla_solver_impl::get_model() {
  uint64_t generation = m_generation;
  if (m_sat_generation != m_generation) {
    ERR << "Bitwuzla adapter: get_model needs the last check to be sat, with "
           "no change since; this model has no values";
    generation = 0;
  }
  return std::make_shared<bitwuzla_model_impl>(m_self, generation);
}

Expr bitwuzla_solver_impl::eval_in_model(Expr e, uint64_t generation) {
  if (generation != m_generation) {
    ERR << "Bitwuzla adapter: a model was used after the solver changed, or "
           "after a check that was not sat; it has no values";
    return mk<NONDET>(e->efac());
  }
  // -- a struct, field by field, as Z3's model does (Z3.hh:399-405). Formulas
  // -- have no structs, but with --horn-bv2-extra-widemem SeaHorn asks for
  // -- registers that are structs of terms: pointers and memories.
  if (isOpX<MK_STRUCT>(e)) {
    ExprVector fields;
    for (auto it = e->args_begin(), end = e->args_end(); it != end; ++it)
      fields.push_back(eval_in_model(*it, generation));
    return strct::mk(fields);
  }
  if (m_narrow_array_eq) {
    LOG("bitwuzla", WARN << "Bitwuzla model has no values: an assertion has "
                            "an equality between arrays with narrow indices";);
    return mk<NONDET>(e->efac());
  }
  if (m_quantified) {
    LOG("bitwuzla", WARN << "Bitwuzla model has no values: an assertion has "
                            "a quantifier";);
    return mk<NONDET>(e->efac());
  }
  if (m_assumed_narrow_array_eq || m_assumed_quantified) {
    LOG("bitwuzla", WARN << "Bitwuzla model has no values: an assumption has "
                            "a quantifier or an equality between arrays with "
                            "narrow indices";);
    return mk<NONDET>(e->efac());
  }
  try {
    bitwuzla::Term t = m_marshal.encode_term(e);
    // -- (a search of its own: an array equality of any width counts here)
    std::unordered_set<bitwuzla::Term> none;
    if (hasArrayEquality(t, none, std::numeric_limits<uint64_t>::max())) {
      LOG("bitwuzla", WARN << "Bitwuzla model does not evaluate equalities "
                              "between arrays";);
      return mk<NONDET>(e->efac());
    }
    if (hasQuantifier(t, m_no_quantifier)) {
      LOG("bitwuzla", WARN << "Bitwuzla model does not evaluate quantifiers";);
      return mk<NONDET>(e->efac());
    }
    if (Expr v = decode_bitwuzla_value(m_bzla->get_value(t), e->efac()))
      return v;
    LOG("bitwuzla", WARN << "Bitwuzla model: no value for a term of sort "
                         << t.sort().str(););
  } catch (std::exception &ex) {
    // -- UnsupportedExpr, or a bitwuzla::Exception
    LOG("bitwuzla", WARN << "Bitwuzla model cannot evaluate: " << ex.what(););
  }
  return mk<NONDET>(e->efac());
}

void bitwuzla_solver_impl::print_model(llvm::raw_ostream &o,
                                       uint64_t generation) {
  if (generation != m_generation) {
    ERR << "Bitwuzla adapter: a model was printed after the solver changed, "
           "or after a check that was not sat; it has no values";
    return;
  }
  // -- the constants of the assertions and of the last check's assumptions,
  // -- without recursion (formulas can be deep), sorted by name
  std::vector<std::pair<std::string, Expr>> consts;
  ExprSet seen;
  ExprVector todo(m_assertions.begin(), m_assertions.end());
  for (auto &ta : m_assumptions)
    todo.push_back(ta.second);
  while (!todo.empty()) {
    Expr e = todo.back();
    todo.pop_back();
    if (!seen.insert(e).second)
      continue;
    if (bind::IsConst()(e)) {
      std::string name;
      llvm::raw_string_ostream os(name);
      os << *e;
      consts.push_back({os.str(), e});
      continue;
    }
    todo.insert(todo.end(), e->args_begin(), e->args_end());
  }
  std::stable_sort(
      consts.begin(), consts.end(),
      [](const auto &a, const auto &b) { return a.first < b.first; });
  for (auto &c : consts)
    o << c.first << " = " << *eval_in_model(c.second, generation) << "\n";
}

void bitwuzla_solver_impl::to_smt_lib(llvm::raw_ostream &o) {
  // -- without an assertion, it would be another formula
  const std::string &why = !m_lost.empty() ? m_lost : m_unsupported;
  if (!why.empty()) {
    ERR << "Bitwuzla adapter: no SMT-LIB formula written: " << why;
    o << "; Bitwuzla adapter: no formula written: " << oneLine(why) << "\n";
    return;
  }
  try {
    bool lambda_left = false;
    std::string text = printSmtLib(m_tm, m_terms, levels(), &lambda_left);
    if (lambda_left)
      WARN << "Bitwuzla adapter: the SMT-LIB formula has a lambda that is not "
              "applied, which the bitwuzla parser cannot read";
    o << text;
  } catch (std::exception &ex) {
    ERR << "Bitwuzla adapter: cannot write the SMT-LIB formula: " << ex.what();
    o << "; Bitwuzla adapter: no formula written: " << oneLine(ex.what())
      << "\n";
  }
}

} // namespace solver
} // namespace seahorn

#endif
