#include "seahorn/SolverBmc.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"
#include "seahorn/UfoOpSem.hh"

#include "llvm/ADT/STLExtras.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Bmc.hh"
#include "seahorn/CallUtils.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn {
/* use options from Bmc.cc*/
extern std::string BmcSmtLogic;
extern std::string BmcSmtTactic;
} // namespace seahorn

namespace seahorn {
SolverBmcEngine::SolverBmcEngine(OperationalSemantics &sem,
                                 solver::SolverKind solver_kind)
    : m_sem(sem), m_efac(sem.efac()), m_result(solver::SolverResult::UNKNOWN),
      m_cpg(nullptr), m_fn(nullptr), m_ctxState(m_efac),
      m_solver_kind(solver_kind) {

  if (m_solver_kind == solver::SolverKind::Z3) {
    LOG("bmc", INFO << "bmc using Z3";);
    z3n_set_param(":model.compact", false);
    if (BmcSmtTactic != "default")
      z3n_set_param(":tactic.default_tactic", BmcSmtTactic.c_str());
    m_new_smt_solver = std::make_unique<solver::z3_solver_impl>(sem.efac());
  } else if (m_solver_kind == solver::SolverKind::YICES2) {
    LOG("bmc", INFO << "bmc using Yices2";);
#ifdef WITH_YICES2
    const char *logic = (BmcSmtLogic == "ALL") ? nullptr : BmcSmtLogic.c_str();
    m_new_smt_solver =
        std::make_unique<solver::yices_solver_impl>(sem.efac(), logic);
#else
    ERR << "No yices2 fiound. Compile SeaHorn with YICES2_HOME option!";
    std::exit(1);
#endif
  } else {
    ERR << "Unsupported SMT solver requested\n";
    std::exit(1);
  }
}

void SolverBmcEngine::addCutPoint(const CutPoint &cp) {
  if (m_cps.empty()) {
    m_cpg = &cp.parent();
    m_fn = cp.bb().getParent();
  }

  assert(m_cpg == &cp.parent());
  m_cps.push_back(&cp);
}

solver::SolverResult SolverBmcEngine::solve() {
  encode();
  m_result = m_new_smt_solver->check();
  return m_result;
}

void SolverBmcEngine::encode(bool assert_formula) {

  // -- only run the encoding once
  if (m_semCtx)
    return;

  assert(m_cpg);
  assert(m_fn);

  m_semCtx = m_sem.mkContext(m_ctxState, m_side);
  VCGen vcgen(m_sem);

  // first state is the state in which execution starts
  m_states.push_back(m_semCtx->values());

  // -- for every pair of cut-points
  const CutPoint *prev = nullptr;
  for (const CutPoint *cp : m_cps) {
    if (prev) {
      const CpEdge *edg = m_cpg->getEdge(*prev, *cp);
      assert(edg);
      m_edges.push_back(edg);

      // generate vc for current edge
      vcgen.genVcForCpEdge(*m_semCtx, *edg);
      // store a copy of the state at the end of execution
      m_states.push_back(m_semCtx->values());
    }
    prev = cp;
  }

  if (assert_formula) {
    for (Expr v : m_side)
      m_new_smt_solver->add(v);
  }
}

void SolverBmcEngine::reset() {
  m_cps.clear();
  m_cpg = nullptr;
  m_fn = nullptr;
  m_new_smt_solver->reset();

  m_side.clear();
  m_states.clear();
  m_edges.clear();
}

/// output current path condition in SMT-LIB2 format
raw_ostream &SolverBmcEngine::toSmtLib(raw_ostream &out) {
  encode();
  m_new_smt_solver->to_smt_lib(out);
  return out;
}

SolverBmcTraceTy SolverBmcEngine::getTrace() {
  assert(m_result == solver::SolverResult::SAT);
  auto model = m_new_smt_solver->get_model();
  return SolverBmcTraceTy(*this, model);
}

} // namespace seahorn
