#ifdef WITH_YICES2
/* Unit tests for yices2 and generic solver and model */

#include "seahorn/Expr/Smt/MarshalYices.hh"
#include "seahorn/Expr/Smt/Model.hh"
#include "seahorn/Expr/Smt/Solver.hh"
#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#include "seahorn/Expr/Smt/Z3SolverImpl.hh"

#include "llvm/Support/raw_ostream.h"

#include "doctest.h"

using namespace std;
using namespace expr;
using namespace seahorn;

static void run(seahorn::solver::Solver *s, Expr e,
                const ExprVector &model_vars) {
  s->push();
  if (bool success = s->add(e)) {
    seahorn::solver::SolverResult answer = s->check();
    if (answer == seahorn::solver::SolverResult::ERROR) {
      errs() << "Solver::check failed!\n";
    } else {
      if (answer == seahorn::solver::SolverResult::SAT) {
        errs() << "SAT\n";
        seahorn::solver::Solver::model_ref model = s->get_model();
        for (unsigned i = 0, e = model_vars.size(); i < e; ++i) {
          Expr valx = model->eval(model_vars[i], false);
          llvm::errs() << "val" << *model_vars[i] << " = " << *valx << "\n";
        }
        errs() << *model << "\n";
      } else if (answer == seahorn::solver::SolverResult::UNSAT) {
        errs() << "UNSAT\n";
      } else {
        errs() << "UNKNOWN\n";
      }
    }
  } else {
    errs() << "Solver:add failed!\n";
  }
  s->pop();
}

static void unsat_core(seahorn::solver::Solver *s, const ExprVector &f,
                       ExprVector &out) {

  s->push();

  // for each v in f we create an impliciation b -> v
  // where b is a boolean
  ExprVector assumptions;
  assumptions.reserve(f.size());
  for (Expr v : f) {
    Expr a = bind::boolConst(mk<ASM>(v));
    assumptions.push_back(a);
    s->add(mk<IMPL>(a, v));
  }

  seahorn::solver::SolverResult res = s->check_with_assumptions(assumptions);
  if (res == seahorn::solver::SolverResult::UNSAT) {
    s->unsat_core(out);
  }

  // unwrap the core from ASM to corresponding expressions
  for (unsigned i = 0, e = out.size(); i < e; ++i) {
    out[i] = bind::fname(bind::fname(out[i]))->arg(0);
  }

  s->pop();
}

TEST_CASE("yices2-int.test") {

  expr::ExprFactory efac;

  seahorn::solver::yices_solver_impl yices_solver(efac);
  seahorn::solver::Solver *ysolver = &yices_solver;
  seahorn::solver::z3_solver_impl z3_solver(efac);
  seahorn::solver::Solver *zsolver = &z3_solver;

  Expr x = bind::intConst(mkTerm<string>("x", efac));
  Expr y = bind::intConst(mkTerm<string>("y", efac));
  Expr z = bind::intConst(mkTerm<string>("z", efac));
  Expr e1 = mk<EQ>(x, mkTerm<expr::mpz_class>(0, efac));
  Expr e2 = mk<EQ>(y, mkTerm<expr::mpz_class>(5, efac));
  Expr e3 = mk<EQ>(z, mkTerm<expr::mpz_class>(10, efac));
  Expr e4 = mk<GT>(x, y);
  Expr e5 = mk<GT>(y, x);

  std::vector<Expr> args({e1, e2, e5});
  Expr e = mknary<AND>(args.begin(), args.end());
  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  errs() << "Result: ";
  run(ysolver, e, {x, y});

  errs() << "==== Z3\n";
  errs() << "Result: ";
  run(zsolver, e, {x, y});

  ExprVector fv({e1, e2, e3, e4});
  Expr f = mknary<AND>(fv.begin(), fv.end());
  errs() << "\n\nAsserting " << *f << "\n";

  errs() << "==== Yices2\n";
  errs() << "Result: ";
  ysolver->reset();
  run(ysolver, f, {});
  ExprVector core;
  unsat_core(ysolver, fv, core);
  errs() << "unsat core = " << *(mknary<AND>(core.begin(), core.end())) << "\n";

  errs() << "==== Z3\n";
  errs() << "Result: ";
  zsolver->reset();
  run(zsolver, f, {});
  core.clear();
  unsat_core(zsolver, fv, core);
  errs() << "unsat core = " << *(mknary<AND>(core.begin(), core.end())) << "\n";

  errs() << "FINISHED\n\n\n";

  CHECK(true);
}

TEST_CASE("yices2-bv.test") {
  using namespace std;
  using namespace expr;
  using namespace seahorn;

  expr::ExprFactory efac;

  Expr x = op::bv::bvConst(mkTerm<string>("x", efac), 32);
  Expr y = op::bv::bvConst(mkTerm<string>("y", efac), 32);

  Expr e1 = mk<EQ>(x, op::bv::bvnum(0, 32, efac));
  Expr e2 = mk<EQ>(y, op::bv::bvnum(5, 32, efac));
  Expr e3 = mk<BSGT>(x, y);
  Expr e4 = mk<BSGT>(y, x);

  std::vector<Expr> args({e1, e2, e4});
  Expr e = mknary<AND>(args.begin(), args.end());

  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  seahorn::solver::yices_solver_impl yices_solver(efac);
  errs() << "Result: ";
  run(&yices_solver, e, {x, y});

  errs() << "==== Z3\n";
  seahorn::solver::z3_solver_impl z3_solver(efac);
  errs() << "Result: ";
  run(&z3_solver, e, {x, y});

  errs() << "FINISHED\n\n\n";
  CHECK(true);
}

TEST_CASE("yices2-int-arr.test") {
  using namespace std;
  using namespace expr;
  using namespace seahorn;

  expr::ExprFactory efac;

  // integer variables
  Expr i = bind::intConst(mkTerm<string>("i", efac));
  Expr j = bind::intConst(mkTerm<string>("j", efac));
  Expr x = bind::intConst(mkTerm<string>("x", efac));
  Expr y = bind::intConst(mkTerm<string>("y", efac));

  // array variables
  Expr intTy = sort::intTy(efac);
  Expr ty = sort::arrayTy(intTy, intTy);
  Expr a1 = bind::mkConst(mkTerm<string>("a1", efac), ty);
  Expr a2 = bind::mkConst(mkTerm<string>("a2", efac), ty);
  Expr a3 = bind::mkConst(mkTerm<string>("a3", efac), ty);

  Expr e1 = mk<EQ>(i, mkTerm<expr::mpz_class>(0, efac));
  Expr e2 = mk<EQ>(j, mkTerm<expr::mpz_class>(1, efac));
  Expr e3 = mk<EQ>(x, mkTerm<expr::mpz_class>(3, efac));
  Expr e4 = mk<EQ>(y, mkTerm<expr::mpz_class>(5, efac));
  Expr e5 = mk<EQ>(a2, op::array::store(a1, i, x));
  Expr e6 = mk<EQ>(a3, op::array::store(a2, j, y));
  Expr e7 = mk<GT>(op::array::select(a3, i), op::array::select(a3, j));
  Expr e8 = mk<GT>(op::array::select(a3, j), op::array::select(a3, i));

  std::vector<Expr> args({e1, e2, e3, e4, e5, e6, e8});
  Expr e = mknary<AND>(args.begin(), args.end());

  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  seahorn::solver::yices_solver_impl yices_solver(efac);
  errs() << "Result: ";
  run(&yices_solver, e, {x, y, a3});

  errs() << "==== Z3\n";
  seahorn::solver::z3_solver_impl z3_solver(efac);
  errs() << "Result: ";
  run(&z3_solver, e, {x, y, a3});

  errs() << "FINISHED\n";

  CHECK(true);
}

TEST_CASE("yices2-int-bv.test") {
  using namespace std;
  using namespace expr;
  using namespace seahorn;

  expr::ExprFactory efac;

  // integer variables
  Expr i = bind::intConst(mkTerm<string>("i", efac));
  Expr j = bind::intConst(mkTerm<string>("j", efac));
  // bv variables
  Expr x = op::bv::bvConst(mkTerm<string>("x", efac), 32);
  Expr y = op::bv::bvConst(mkTerm<string>("y", efac), 32);

  // array variables
  Expr intTy = sort::intTy(efac);
  Expr bvTy = op::bv::bvsort(32, efac);
  Expr ty = sort::arrayTy(intTy, bvTy);
  Expr a1 = bind::mkConst(mkTerm<string>("a1", efac), ty);
  Expr a2 = bind::mkConst(mkTerm<string>("a2", efac), ty);
  Expr a3 = bind::mkConst(mkTerm<string>("a3", efac), ty);

  Expr e1 = mk<EQ>(i, mkTerm<expr::mpz_class>(0, efac));
  Expr e2 = mk<EQ>(j, mkTerm<expr::mpz_class>(1, efac));

  Expr e3 = mk<EQ>(x, op::bv::bvnum(0, 32, efac));
  Expr e4 = mk<EQ>(y, op::bv::bvnum(5, 32, efac));
  Expr e5 = mk<EQ>(a2, op::array::store(a1, i, x));
  Expr e6 = mk<EQ>(a3, op::array::store(a2, j, y));
  Expr e7 = mk<BSGT>(op::array::select(a3, i), op::array::select(a3, j));
  Expr e8 = mk<BSGT>(op::array::select(a3, j), op::array::select(a3, i));

  std::vector<Expr> args({e1, e2, e3, e4, e5, e6, e8});
  Expr e = mknary<AND>(args.begin(), args.end());

  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  seahorn::solver::yices_solver_impl yices_solver(efac);
  errs() << "Result: ";
  run(&yices_solver, e, {x, y, a3});

  errs() << "==== Z3\n";
  seahorn::solver::z3_solver_impl z3_solver(efac);
  errs() << "Result: ";
  run(&z3_solver, e, {x, y, a3});

  errs() << "FINISHED\n";

  CHECK(true);
}

TEST_CASE("yices2-const-array.test") {
  using namespace std;
  using namespace expr;
  using namespace seahorn;

  expr::ExprFactory efac;

  size_t BV_SZ = 32;
  size_t IDX_SZ = 8;
  // index variables
  Expr i = op::bv::bvConst(mkTerm<string>("i", efac), IDX_SZ);
  // arr variables
  Expr iTy = op::bv::bvsort(IDX_SZ, efac);
  Expr y = op::bv::bvConst(mkTerm<string>("y", efac), BV_SZ);
  Expr arr = op::array::constArray(iTy, y);

  // testing marshaling so UNSAT is fine, yices2 has problem extracting
  // assignments from lambda terms
  Expr e = mk<NEQ>(op::array::select(arr, i), y);

  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  seahorn::solver::yices_solver_impl yices_solver(efac);
  errs() << "Result: ";
  run(&yices_solver, e, {arr, y, i});

  errs() << "==== Z3\n";
  seahorn::solver::z3_solver_impl z3_solver(efac);
  errs() << "Result: ";
  run(&z3_solver, e, {arr, y, i});

  errs() << "FINISHED\n";

  CHECK(true);
}

#endif
