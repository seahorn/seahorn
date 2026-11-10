#ifdef WITH_BITWUZLA

#include "seahorn/Expr/Smt/BitwuzlaSolverImpl.hh"
#include "seahorn/Expr/Smt/BitwuzlaEncodingCheck.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/raw_ostream.h"

#include <chrono>
#include <cstdlib>
#include <fstream>
#include <unistd.h>

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

bitwuzla_solver_impl::bitwuzla_solver_impl() : Solver(), m_marshal(m_tm) {
  // -- options must be set before the Bitwuzla instance is created
  m_options.set(Option::PRODUCE_MODELS, true);
  m_bzla = mkBitwuzla(m_tm, m_options);
}

bitwuzla_solver_impl::~bitwuzla_solver_impl() = default;

bool bitwuzla_solver_impl::add(Expr exp) {
  try {
    bitwuzla::Term t = m_marshal.encode_term(exp);
    if (!CheckEncodingLog.empty())
      checkEncoding(exp, t);
    m_bzla->assert_formula(t);
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
  if (!m_unsupported.empty()) {
    LOG("bitwuzla", WARN << "answering unknown: " << m_unsupported;);
    return SolverResult::UNKNOWN;
  }
  try {
    switch (m_bzla->check_sat()) {
    case bitwuzla::Result::SAT:
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
  // -- a fresh instance; the TermManager and the encoder's cache stay valid
  m_bzla.reset();
  m_bzla = mkBitwuzla(m_tm, m_options);
  m_unsupported.clear();
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

bitwuzla_solver_impl::model_ref bitwuzla_solver_impl::get_model() {
  notSupportedYet("get_model (models and traces)");
}

void bitwuzla_solver_impl::to_smt_lib(llvm::raw_ostream &o) {
  notSupportedYet("to_smt_lib");
}

} // namespace solver
} // namespace seahorn

#endif
