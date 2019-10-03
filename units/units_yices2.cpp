#ifdef WITH_YICES2
#include "seahorn/Expr/Smt/ZExprConverter.hh"
#include "seahorn/Expr/Smt/Solver.hh"
#include "seahorn/Expr/Smt/Yices2SolverImpl.hh"
#include "seahorn/Expr/Smt/Z3SolverImpl.hh"
#include "seahorn/Expr/Smt/Model.hh"
#include "seahorn/Expr/Smt/MarshalYices.hh"

#include "llvm/Support/raw_ostream.h"

#include "doctest.h"

using namespace std;
using namespace expr;
using namespace ufo;

static void run(seahorn::solver::Solver *s, Expr e, const ExprVector& model_vars) {
  if (bool success = s->add(e)){
    seahorn::solver::Solver::result answer = s->check();
    if(answer == seahorn::solver::Solver::ERROR){
      errs() << "Solver::check failed!\n";
    } else {
      if (answer == seahorn::solver::Solver::SAT){
	errs() << "SAT\n";
	seahorn::solver::Solver::model_ref model = s->get_model();
	for(unsigned i=0,e=model_vars.size();i<e;++i) {
	  Expr valx = model->eval(model_vars[i], false);
	  llvm::errs () << "val" << *model_vars[i] << " = " << *valx  << "\n";
	}
	errs () << *model << "\n";
      } else if (answer == seahorn::solver::Solver::UNSAT) {
	errs() << "UNSAT\n";	
      } else {
	errs() << "UNKNOWN\n";	
      }
    }
  } else {
    errs () << "Solver:add failed!\n";
  }
}

TEST_CASE("yices2-int.test") {
  
  seahorn::solver::solver_options opts;
  expr::ExprFactory efac;

  Expr x = bind::intConst (mkTerm<string> ("x", efac));
  Expr y = bind::intConst (mkTerm<string> ("y", efac));

  Expr e1 = mk<EQ>(x, mkTerm<mpz_class>(0, efac));
  Expr e2 = mk<EQ>(y, mkTerm<mpz_class>(5, efac));
  Expr e3 = mk<GT>(x, y);
  Expr e4 = mk<GT>(y, x);

  std::vector<Expr> args({e1, e2, e4});
  Expr e = mknary<AND>(args.begin(), args.end());

  errs() << "Asserting " << *e << "\n";
  
  errs() << "==== Yices2\n";
  seahorn::yices::yices_solver_impl yices_solver(&opts, efac);
  errs() << "Result: ";
  run(&yices_solver, e, {x,y});
  
  errs() << "==== Z3\n";
  EZ3 ctx(efac);
  seahorn::z3::z3_solver_impl z3_solver(&opts,ctx);
  errs() << "Result: ";
  run(&z3_solver, e, {x,y});
  
  errs() << "FINISHED\n\n\n";

  CHECK(true);
}

TEST_CASE("yices2-bv.test") {
  using namespace std;
  using namespace expr;
  using namespace ufo;
  
  seahorn::solver::solver_options opts;
  expr::ExprFactory efac;

  Expr x = op::bv::bvConst (mkTerm<string> ("x", efac), 32);
  Expr y = op::bv::bvConst (mkTerm<string> ("y", efac), 32);

  Expr e1 = mk<EQ>(x, op::bv::bvnum(mpz_class(0), 32, efac));
  Expr e2 = mk<EQ>(y, op::bv::bvnum(mpz_class(5), 32, efac));
  Expr e3 = mk<BSGT>(x, y);
  Expr e4 = mk<BSGT>(y, x);

  std::vector<Expr> args({e1, e2, e4});
  Expr e = mknary<AND>(args.begin(), args.end());

  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  seahorn::yices::yices_solver_impl yices_solver(&opts, efac);
  errs() << "Result: ";
  run(&yices_solver, e, {x,y});
  
  errs() << "==== Z3\n";
  EZ3 ctx(efac);
  seahorn::z3::z3_solver_impl z3_solver(&opts,ctx);
  errs() << "Result: ";
  run(&z3_solver, e, {x,y});
  
  errs() << "FINISHED\n\n\n";
  CHECK(true);
}

TEST_CASE("yices2-int-arr.test") {
  using namespace std;
  using namespace expr;
  using namespace ufo;
  
  seahorn::solver::solver_options opts;
  expr::ExprFactory efac;

  // integer variables
  Expr i = bind::intConst (mkTerm<string> ("i", efac));
  Expr j = bind::intConst (mkTerm<string> ("j", efac));
  Expr x = bind::intConst (mkTerm<string> ("x", efac));
  Expr y = bind::intConst (mkTerm<string> ("y", efac));

  // array variables
  Expr intTy = sort::intTy(efac);
  Expr ty = sort::arrayTy(intTy, intTy);
  Expr a1 = bind::mkConst(mkTerm<string> ("a1", efac), ty);
  Expr a2 = bind::mkConst(mkTerm<string> ("a2", efac), ty);
  Expr a3 = bind::mkConst(mkTerm<string> ("a3", efac), ty);    

  Expr e1 = mk<EQ>(i, mkTerm<mpz_class>(0, efac));
  Expr e2 = mk<EQ>(j, mkTerm<mpz_class>(1, efac));
  Expr e3 = mk<EQ>(x, mkTerm<mpz_class>(3, efac));
  Expr e4 = mk<EQ>(y, mkTerm<mpz_class>(5, efac));
  Expr e5 = mk<EQ>(a2, op::array::store(a1, i, x));
  Expr e6 = mk<EQ>(a3, op::array::store(a2, j, y));
  Expr e7 = mk<GT>(op::array::select(a3,i), op::array::select(a3,j));
  Expr e8 = mk<GT>(op::array::select(a3,j), op::array::select(a3,i));

  std::vector<Expr> args({e1, e2, e3, e4, e5, e6, e8});
  Expr e = mknary<AND>(args.begin(), args.end());

  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  seahorn::yices::yices_solver_impl yices_solver(&opts, efac);
  errs() << "Result: ";
  run(&yices_solver, e, {x,y,a3});
  
  errs() << "==== Z3\n";
  EZ3 ctx(efac);
  seahorn::z3::z3_solver_impl z3_solver(&opts,ctx);
  errs() << "Result: ";
  run(&z3_solver, e, {x,y,a3});
  
  errs() << "FINISHED\n";

  CHECK(true);
}

TEST_CASE("yices2-int-bv.test") {
  using namespace std;
  using namespace expr;
  using namespace ufo;
  
  seahorn::solver::solver_options opts;
  expr::ExprFactory efac;

  // integer variables
  Expr i = bind::intConst (mkTerm<string> ("i", efac));
  Expr j = bind::intConst (mkTerm<string> ("j", efac));
  // bv variables
  Expr x = op::bv::bvConst (mkTerm<string> ("x", efac), 32);
  Expr y = op::bv::bvConst (mkTerm<string> ("y", efac), 32);
  
  // array variables
  Expr intTy = sort::intTy(efac);
  Expr bvTy = op::bv::bvsort(32, efac);
  Expr ty = sort::arrayTy(intTy, bvTy);
  Expr a1 = bind::mkConst(mkTerm<string> ("a1", efac), ty);
  Expr a2 = bind::mkConst(mkTerm<string> ("a2", efac), ty);
  Expr a3 = bind::mkConst(mkTerm<string> ("a3", efac), ty);    

  Expr e1 = mk<EQ>(i, mkTerm<mpz_class>(0, efac));
  Expr e2 = mk<EQ>(j, mkTerm<mpz_class>(1, efac));

  
  Expr e3 = mk<EQ>(x, op::bv::bvnum(mpz_class(0), 32, efac));
  Expr e4 = mk<EQ>(y, op::bv::bvnum(mpz_class(5), 32, efac));
  Expr e5 = mk<EQ>(a2, op::array::store(a1, i, x));
  Expr e6 = mk<EQ>(a3, op::array::store(a2, j, y));
  Expr e7 = mk<BSGT>(op::array::select(a3,i), op::array::select(a3,j));
  Expr e8 = mk<BSGT>(op::array::select(a3,j), op::array::select(a3,i));

  std::vector<Expr> args({e1, e2, e3, e4, e5, e6, e8});
  Expr e = mknary<AND>(args.begin(), args.end());

  errs() << "Asserting " << *e << "\n";

  errs() << "==== Yices2\n";
  seahorn::yices::yices_solver_impl yices_solver(&opts, efac);
  errs() << "Result: ";
  run(&yices_solver, e, {x,y,a3});
  
  errs() << "==== Z3\n";
  EZ3 ctx(efac);
  seahorn::z3::z3_solver_impl z3_solver(&opts,ctx);
  errs() << "Result: ";
  run(&z3_solver, e, {x,y,a3});
  
  errs() << "FINISHED\n";

  CHECK(true);
}

#endif 
