#include "seahorn/Bmc.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"
#include "seahorn/UfoOpSem.hh"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/HexDump.hh"
#include "seahorn/Support/SeaDebug.h"

namespace seahorn {
std::string BmcSmtLogic;
std::string BmcSmtTactic;
bool DumpHex;
} // namespace seahorn

static llvm::cl::opt<bool, true>
    XDumpHex("horn-bmc-hexdump",
             llvm::cl::desc("Dump memory state using hexdump"),
             llvm::cl::location(seahorn::DumpHex), cl::init(false));
static llvm::cl::opt<std::string, true>
    XBmcSmtTactic("horn-bmc-tactic", llvm::cl::desc("Z3 tactic to use for BMC"),
                  llvm::cl::location(seahorn::BmcSmtTactic),
                  cl::init("default"));
static llvm::cl::opt<std::string, true>
    XBmcSmtLogic("horn-bmc-logic",
                 llvm::cl::desc("SMT-LIB logic to pass to smt solver"),
                 llvm::cl::location(seahorn::BmcSmtLogic), cl::init("ALL"));

namespace seahorn {
BmcEngine::BmcEngine(OperationalSemantics &sem, EZ3 &zctx)
    : m_sem(sem), m_efac(sem.efac()), m_result(boost::indeterminate),
      m_cpg(nullptr), m_fn(nullptr), m_smt_solver(zctx, BmcSmtLogic.c_str()),
      m_ctxState(m_efac) {

  z3n_set_param(":model.compact", false);
  if (BmcSmtTactic != "default") {
    z3n_set_param(":tactic.default_tactic", BmcSmtTactic.c_str());
    if (BmcSmtTactic == "sat" || llvm::StringRef(BmcSmtTactic).endswith("sat)"))
      z3n_set_param(":sat.euf", true);
  }
}

void BmcEngine::addCutPoint(const CutPoint &cp) {
  if (m_cps.empty()) {
    m_cpg = &cp.parent();
    m_fn = cp.bb().getParent();
  }

  assert(m_cpg == &cp.parent());
  m_cps.push_back(&cp);
}

boost::tribool BmcEngine::solve() {
  encode();
  m_result = m_smt_solver.solve();
  return m_result;
}

void BmcEngine::encode(bool assert_formula) {

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
      m_smt_solver.assertExpr(v);
  }
}

void BmcEngine::reset() {
  m_cps.clear();
  m_cpg = nullptr;
  m_fn = nullptr;
  m_smt_solver.reset();

  m_side.clear();
  m_states.clear();
  m_edges.clear();
}

void BmcEngine::unsatCore(ExprVector &out) {
  const bool simplify = true;
  bmc_impl::unsat_core(m_smt_solver, m_side, simplify, out);
}

/// output current path condition in SMT-LIB2 format
raw_ostream &BmcEngine::toSmtLib(raw_ostream &out) {
  if (BmcSmtLogic != "ALL") {
    out << "(set-logic " << BmcSmtLogic << ")\n";
    if (BmcSmtLogic == "QF_AUFBV") {
      // -- provide definition of mul with overflow
      // XXX 64 bit definition because we don't know the current register size
      out << "(define-fun bvumul_noovfl ((x (_ BitVec 64)) (y (_ BitVec 64))) "
             "Bool\n"
          << "(ite (= x #x0000000000000000) true (= (bvudiv (bvmul x y) x) y)) "
             ")\n";
    }
  }
  encode();
  return m_smt_solver.toSmtLib(out);
}

ZBmcTraceTy BmcEngine::getTrace() {
  assert((bool)m_result);
  auto model = m_smt_solver.getModel();
  return ZBmcTraceTy(*this, model);
}

namespace bmc_impl {

bool isCallToVoidFn(const llvm::Instruction &I) {
  if (const CallInst *ci = dyn_cast<const CallInst>(&I))
    if (const Function *fn = ci->getCalledFunction())
      return fn->getReturnType()->isVoidTy();

  return false;
}

void unsat_core(ZSolver<EZ3> &solver, const ExprVector &f, bool simplify,
                ExprVector &out) {
  solver.reset();
  ExprVector assumptions;
  assumptions.reserve(f.size());
  for (Expr v : f) {
    Expr a = bind::boolConst(mk<ASM>(v));
    assumptions.push_back(a);
    solver.assertExpr(mk<IMPL>(a, v));
  }

  ExprVector core;
  solver.push();
  boost::tribool res = solver.solveAssuming(assumptions);
  if (!res)
    solver.unsatCore(std::back_inserter(core));
  solver.pop();
  if (res)
    return;

  if (simplify) {
    // simplify core
    while (core.size() < assumptions.size()) {
      assumptions.assign(core.begin(), core.end());
      core.clear();
      solver.push();
      res = solver.solveAssuming(assumptions);
      assert(!res ? 1 : 0);
      solver.unsatCore(std::back_inserter(core));
      solver.pop();
    }

    // minimize simplified core
    for (unsigned i = 0; i < core.size();) {
      Expr saved = core[i];
      core[i] = core.back();
      res = solver.solveAssuming(
          boost::make_iterator_range(core.begin(), core.end() - 1));
      if (res)
        core[i++] = saved;
      else if (!res)
        core.pop_back();
      else
        assert(0);
    }
  }

  // unwrap the core from ASM to corresponding expressions
  for (Expr c : core)
    out.push_back(bind::fname(bind::fname(c))->arg(0));
}

/* specialization for llvm::raw_ostream */
template <>
void dump_evaluated_inst(const Instruction &inst, Expr v, raw_ostream &out,
                         bool shadow_mem) {
  if (out.has_colors())
    out.changeColor(raw_ostream::RED);
  if (DumpHex && shadow_mem) {
    using HD = expr::hexDump::HexDump;
    using SHD = expr::hexDump::StructHexDump;
    out << "  %" << inst.getName() << "\n";

    if (isOp<MK_STRUCT>(v)) {
      out << SHD(v);
    } else {
      out << HD(v);
    }

  } else
    out << "  %" << inst.getName() << " " << *v;

  const DebugLoc &dloc = inst.getDebugLoc();
  if (dloc) {
    if (out.has_colors())
      out.changeColor(raw_ostream::CYAN);
    out << " [" << (*dloc).getFilename() << ":" << dloc.getLine() << "]";
  }
  out << "\n";
  out.resetColor();
}

} // end namespace bmc_impl

} // namespace seahorn
