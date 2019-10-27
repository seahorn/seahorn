#include "seahorn/PathBmcMuc.hh"
#include "seahorn/PathBmcUtil.hh"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/Solver.hh"

namespace seahorn {
namespace path_bmc {

using namespace expr;

void muc_with_assumptions::unsat_core(const ExprVector &f, bool simplify,
                                      ExprVector &out) {

  m_solver.reset();
  ExprVector assumptions;
  assumptions.reserve(f.size());
  for (Expr v : f) {
    Expr a = bind::boolConst(mk<ASM>(v));
    assumptions.push_back(a);
    m_solver.add(mk<IMPL>(a, v));
  }

  ExprVector core;
  m_solver.push();
  solver::SolverResult res = m_solver.check_with_assumptions(assumptions);
  if (res == solver::SolverResult::UNSAT) {
    m_solver.unsat_core(core);
  }
  m_solver.pop();
  if (res == solver::SolverResult::SAT) {
    return;
  }

  if (simplify) {
    // simplify core
    while (core.size() < assumptions.size()) {
      assumptions.assign(core.begin(), core.end());
      core.clear();
      m_solver.push();
      res = m_solver.check_with_assumptions(assumptions);
      assert(res == solver::SolverResult::UNSAT);
      m_solver.unsat_core(core);
      m_solver.pop();
    }

    // minimize simplified core
    for (unsigned i = 0; i < core.size();) {
      Expr saved = core[i];
      core[i] = core.back();
      res = m_solver.check_with_assumptions(
          llvm::make_range(core.begin(), core.end() - 1));
      if (res == solver::SolverResult::SAT)
        core[i++] = saved;
      else if (res == solver::SolverResult::UNSAT)
        core.pop_back();
      else
        assert(0);
    }
  }

  // unwrap the core from ASM to corresponding expressions
  for (Expr c : core)
    out.push_back(bind::fname(bind::fname(c))->arg(0));
}

muc_with_assumptions::muc_with_assumptions(solver::Solver &solver)
    : minimal_unsat_core(solver) {}

void muc_with_assumptions::run(const ExprVector &f, ExprVector &core) {
  const bool simplify = false;
  unsat_core(f, false, core);
}

solver::SolverResult deletion_muc::check(deletion_muc::const_iterator it,
                                         deletion_muc::const_iterator et,
                                         const ExprVector &assumptions) {
  m_solver.reset();
  for (Expr e : assumptions) {
    m_solver.add(e);
  }
  for (Expr e : llvm::make_range(it, et)) {
    m_solver.add(e);
  }
  solver::SolverResult res;
  {
    path_bmc::scoped_solver ss(m_solver, m_timeout);
    res = ss.get().check();
  }
  return res;
}

void deletion_muc::run(const ExprVector &f, const ExprVector &assumptions,
                       ExprVector &out) {
  assert(check(f.begin(), f.end(), assumptions) == solver::SolverResult::UNSAT);

  out.insert(out.end(), f.begin(), f.end());
  for (unsigned i = 0; i < out.size();) {
    Expr saved = out[i];
    out[i] = out.back();
    auto res = check(out.begin(), out.end() - 1, assumptions);
    if (res == solver::SolverResult::SAT) {
      out[i++] = saved;
    } else if (res == solver::SolverResult::UNSAT) {
      out.pop_back();
    } else {
      // timeout
      out.assign(f.begin(), f.end());
      return;
    }
  }
}

deletion_muc::deletion_muc(solver::Solver &solver, unsigned timeout)
    : minimal_unsat_core(solver), m_timeout(timeout) {}

void deletion_muc::run(const ExprVector &f, ExprVector &out) {
  ExprVector assumptions;
  run(f, assumptions, out);
}

/*
  Compute minimal unsatisfiable cores based on Junker's QuickXplain.

  qx(base, target, skip) {
     if (not skip) and unsat(base) then
          return empty;
     if target is singleton then
          return target

     <t1, t2> := partition(target);
     c1 := qx(base U t2, t1, t2 == empty);  // minimize first half wrt second
     half c2 := qx(base U c1, t2, c1 == empty);  // minimize second half wrt MUS
     of first half. return c1 U c2;
  }
  call qx(empty, formula, false);
*/
void binary_search_muc::qx(const ExprVector &target, unsigned begin,
                           unsigned end, bool skip, ExprVector &out) {
  if (!skip) {
    path_bmc::scoped_solver ss(m_solver, m_timeout);
    auto res = ss.get().check();
    if (res == solver::SolverResult::UNSAT) {
      return;
    }
  }

  if (end - begin == 1) {
    out.push_back(target[begin]);
    return;
  }

  assert(begin < end);
  unsigned mid = (begin + end) / 2;

#if 1
  m_solver.push();
  for (auto it = target.begin() + mid, et = target.begin() + end; it != et;
       ++it) {
    m_solver.add(*it);
  }
  unsigned old_out_size = out.size();
  // minimize 1st half wrt 2nd half
  qx(target, begin, mid, end - mid < 1, out);
  m_solver.pop();
  m_solver.push();
  for (unsigned i = old_out_size, e = out.size(); i < e; ++i) {
    m_solver.add(out[i]);
  }
  // minimize 2nd half wrt MUS(1st half)
  qx(target, mid, end, out.size() - old_out_size < 1, out);
  m_solver.pop();
#else
  m_solver.push();
  for (auto it = target.begin() + begin, et = target.begin() + mid; it != et;
       ++it) {
    m_solver.add(*it);
  }
  unsigned old_out_size = out.size();
  // minimize 2nd half wrt 1st half
  qx(target, mid, end, mid - begin < 1, out);
  m_solver.pop();
  m_solver.push();
  for (unsigned i = old_out_size, e = out.size(); i < e; ++i) {
    m_solver.add(out[i]);
  }
  // minimize 1st half wrt MUS(2nd half)
  qx(target, begin, mid, out.size() - old_out_size < 1, out);
  m_solver.pop();
#endif
}

binary_search_muc::binary_search_muc(solver::Solver &solver, unsigned timeout)
    : minimal_unsat_core(solver), m_timeout(timeout) {}

void binary_search_muc::run(const ExprVector &formula, ExprVector &out) {
  unsigned i = 0;
  unsigned j = formula.size();
  bool skip = false;
  m_solver.reset();
  qx(formula, i, j, skip, out);
}

} // namespace path_bmc
} // namespace seahorn
