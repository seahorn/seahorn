#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/Smt/BitwuzlaEncodingCheck.hh"
#include "seahorn/Expr/Smt/BitwuzlaModelImpl.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <algorithm>
#include <chrono>
#include <cstdlib>
#include <fstream>
#include <unistd.h>
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
static void checkEncoding(Expr exp, const bitwuzla::Term &t) {
  auto start = std::chrono::steady_clock::now();
  EncodingCheck res = checkBitwuzlaEncoding(exp, t, CheckEncodingTimeout);
  long ms = std::chrono::duration_cast<std::chrono::milliseconds>(
                std::chrono::steady_clock::now() - start)
                .count();
  if (res.verdict == EncodingVerdict::DIFFERENT)
    ERR << "Bitwuzla's formula differs from Z3's encoding: " << res.detail;
  logEncodingCheck(verdictName(res.verdict), ms, res.detail);
}

[[noreturn]] static void notSupportedYet(const char *method) {
  ERR << "Bitwuzla adapter: " << method << " is not supported yet";
  std::exit(1);
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

bitwuzla_solver_impl::bitwuzla_solver_impl()
    : Solver(), m_marshal(m_tm),
      m_self(std::make_shared<bitwuzla_solver_impl *>(this)) {
  // -- options must be set before the Bitwuzla instance is created
  m_options.set(Option::PRODUCE_MODELS, true);
  m_bzla = mkBitwuzla(m_tm, m_options);
}

bitwuzla_solver_impl::~bitwuzla_solver_impl() = default;

bool bitwuzla_solver_impl::add(Expr exp) {
  ++m_generation;
  try {
    bitwuzla::Term t = m_marshal.encode_term(exp);
    if (!CheckEncodingLog.empty())
      checkEncoding(exp, t);
    m_bzla->assert_formula(t);
    m_assertions.push_back(exp);
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

SolverResult bitwuzla_solver_impl::check() {
  ++m_generation;
  if (!m_unsupported.empty()) {
    LOG("bitwuzla", WARN << "answering unknown: " << m_unsupported;);
    return SolverResult::UNKNOWN;
  }
  try {
    switch (m_bzla->check_sat()) {
    case bitwuzla::Result::SAT:
      m_sat_generation = m_generation;
      return SolverResult::SAT;
    case bitwuzla::Result::UNSAT:
      return SolverResult::UNSAT;
    case bitwuzla::Result::UNKNOWN:
      return SolverResult::UNKNOWN;
    }
  } catch (std::exception &ex) {
    ERR << "Bitwuzla check failed: " << ex.what();
  }
  return SolverResult::ERROR;
}

void bitwuzla_solver_impl::reset() {
  ++m_generation;
  // -- a fresh instance; the TermManager and the encoder's cache stay valid
  m_bzla.reset();
  m_bzla = mkBitwuzla(m_tm, m_options);
  m_unsupported.clear();
  m_assertions.clear();
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
  try {
    bitwuzla::Term t = m_marshal.encode_term(e);
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
  // -- the constants of the assertions, without recursion (formulas can be
  // -- deep), sorted by name
  std::vector<std::pair<std::string, Expr>> consts;
  ExprSet seen;
  ExprVector todo(m_assertions.begin(), m_assertions.end());
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

SolverResult
bitwuzla_solver_impl::check_with_assumptions(const expr_const_it_range &lits) {
  notSupportedYet("check_with_assumptions");
}

void bitwuzla_solver_impl::unsat_core(ExprVector &out) {
  notSupportedYet("unsat_core");
}

void bitwuzla_solver_impl::push() { notSupportedYet("push"); }

void bitwuzla_solver_impl::pop() { notSupportedYet("pop"); }

void bitwuzla_solver_impl::to_smt_lib(llvm::raw_ostream &o) {
  notSupportedYet("to_smt_lib");
}

} // namespace solver
} // namespace seahorn

#endif
