#include "seahorn/LoadCrab.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/config.h"

#include "llvm/Support/raw_ostream.h"

namespace seahorn {
char LoadCrabPass::ID = 0;
llvm::Pass *createLoadCrabPass() { return new LoadCrabPass(); }
} // namespace seahorn

#ifndef HAVE_CLAM
/// Dummy implementation when Crab is not compiled in
namespace seahorn {
void LoadCrabPass::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool LoadCrabPass::runOnModule(llvm::Module &M) {
  llvm::errs()
      << "WARNING: Not loading invariants. Compiled without Crab support.\n";
  return false;
}
} // namespace seahorn
#else
/// Real implementation starts here
#include "llvm/ADT/DenseMap.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/HornifyModule.hh"

#include "clam/CfgBuilder.hh"
#include "clam/Clam.hh"

#include <unordered_map>

namespace clam {

using namespace llvm;
using namespace expr;
using namespace seahorn;

// Conversion from linear constraints to Expr.
//
// A linear constraint is precisely translated only if all its
// variables can be mapped to a llvm Value. Otherwise, it is
// translated to true. Therefore, constraints involving ghost
// variables might be translated to `true`.
class LinConsToExprImpl {
public:  
  // A normalizer for Boolean constraints
  class BoolCst {
    typedef enum { T_TRUE, T_FALSE, T_TOP } tribool_t;

    tribool_t m_val;

    // internal representation:
    // constraint is of the form m_coef*m_var {<=,==} m_rhs
    // m_coef and m_rhs can be negative numbers.

    number_t m_coef;
    const Value *m_var;
    bool m_is_eq; // tt:equality, ff:inequality
    number_t m_rhs;

  public:
    // If cst is a constraint of the form x<=c where x is a LLVM
    // Value of type i1 then return x, otherwise null.
    static const Value *isBoolCst(lin_cst_t cst) {
      if (cst.is_disequation())
        return nullptr;
      auto e = cst.expression() - cst.expression().constant();
      if (std::distance(e.begin(), e.end()) != 1)
        return nullptr;
      auto t = *(e.begin());
      varname_t v = t.second.name();

      if (!(v.get()))
        return nullptr;

      if ((*(v.get()))->getType()->isIntegerTy(1))
        return *(v.get());
      else
        return nullptr;
    }

    BoolCst(lin_cst_t cst)
        : m_val(T_TOP), m_coef(0), m_rhs(0), m_var(nullptr),
          m_is_eq(cst.is_equality()) {
      assert(isBoolCst(cst));

      auto e = cst.expression() - cst.expression().constant();
      auto t = *(e.begin());
      assert(t.second.name().get());

      m_var = *(t.second.name().get());
      m_coef = t.first;
      m_rhs = -cst.expression().constant();

      if (m_is_eq) {
        if (m_rhs == 0) /* k*x == 0 for any k*/
        {
          m_val = T_FALSE;
        } else if (m_coef == 1 && m_rhs == 1) /*x == 1*/
        {
          m_val = T_TRUE;
        } else if (m_coef == -1 && m_rhs == -1) /*-x == -1*/
        {
          m_val = T_TRUE;
        }
      }
    }

    // Conjoin two boolean constraints
    void operator+=(BoolCst other) {
      // they cannot disagree otherwise the initial constraint
      // would be false.
      assert(!(m_val == T_TRUE && other.m_val == T_FALSE));
      assert(!(m_val == T_FALSE && other.m_val == T_TRUE));

      if (m_val != T_TOP && other.m_val == T_TOP)
        return;
      if (m_val == T_TOP && other.m_val != T_TOP) {
        m_val = other.m_val;
        return;
      }

      if (!m_is_eq && !other.m_is_eq) // both are inequalities
      {

        if (((m_coef == 1 && m_rhs == 0) &&               /* x <= 0*/
             (other.m_coef == -1 && other.m_rhs == 0)) || /*-x <= 0*/
            ((m_coef == -1 && m_rhs == 0) &&              /*-x <= 0*/
             (other.m_coef == 1 && other.m_rhs == 0)))    /* x <= 0*/
        {
          m_val = T_FALSE;
        } else if (((m_coef == 1 && m_rhs == 1) &&                /*x <= 1*/
                    (other.m_coef == -1 && other.m_rhs == -1)) || /*-x <=-1*/
                   ((m_coef == -1 && m_rhs == -1) &&              /*-x <=-1*/
                    (other.m_coef == 1 && other.m_rhs == 1)))     /*x <= 1*/
        {
          m_val = T_TRUE;
        }
      }
    }

    bool isUnknown() const { return m_val == T_TOP; }

    Expr toExpr(ExprFactory &efac,
		const DenseSet<const Value*> *live /*unused*/) const {
      if (isUnknown())
        return mk<TRUE>(efac);

      Expr e = mkTerm<const Value *>(m_var, efac);
      e = bind::boolConst(e);
      if (m_val == T_FALSE)
        return mk<NEG>(e);
      else
        return e;
    }
  };

  
  
private:
  
  const llvm::Function &m_func;
  DenseMap<const Value *, BoolCst> bool_map;
  
  // Defined only for z_number
  Expr exprFromNum(ikos::z_number n, ExprFactory &efac) {
    const expr::mpz_class z(n.get_mpz_t());
    return mkTerm(z, efac);
  }

  Expr exprFromIntVar(varname_t v, ExprFactory &efac,
		      const DenseSet<const Value*> *live) {
    LOG("load-crab-details",
	crab::outs() << "\texprFromIntVar(" << v << ")=";);
    if (!(v.get())) {
      // Skip ghost variables.
      // 
      // v.get() method only returns a non-null value if v contains a
      // const Value*. Otherwise, it means that v refers to a shadow
      // variable which is not currently translated.
      LOG("load-crab-details",crab::outs() << "null\n";);
      return nullptr;
    }
    const Value *V = *(v.get());
    assert(V);
    if (!live || live->count(V) > 0) {
      Expr e = bind::intConst(mkTerm<const Value *>(V, efac));
      LOG("load-crab-details", llvm::errs() << *e << "\n";);
      return e;
    } else {
      LOG("load-crab-details", llvm::errs() << "null\n";);	
      return nullptr;
    }
  }

public:
  LinConsToExprImpl(const CfgBuilder *cfgBuilder /*unused*/, const llvm::Function &func)
    : m_func(func) {}
  
  Expr toExpr(const lin_cst_t &cst, ExprFactory &efac,
	      const DenseSet<const Value*> *live) {
    
    if (cst.is_tautology()) 
      return mk<TRUE>(efac);

    if (cst.is_contradiction())
      return mk<FALSE>(efac);

    LOG("load-crab-details", crab::outs() << "toExpr(" << cst << ")\n";);
    
    // booleans
    if (const Value *v = BoolCst::isBoolCst(cst)) {
      BoolCst b2(cst);
      auto it = bool_map.find(v);
      if (it != bool_map.end()) {
        BoolCst &b1 = it->second;
        b1 += b2;
      } else {
        bool_map.insert(std::make_pair(v, b2));
      }
      LOG("load-crab-details", llvm::errs() << "True\n";);
      return mk<TRUE>(efac); // we ignore cst for now
    }

    // integers
    auto e = cst.expression() - cst.expression().constant();
    Expr ee = exprFromNum(number_t("0"), efac);
    for (auto t : e) {
      number_t n = t.first;
      if (n == 0)
        continue;

      Expr v = exprFromIntVar(t.second.name(), efac, live);
      if (!v) {
        // We could not translate Crab variable.
	LOG("load-crab-details", llvm::errs() << "True\n";);	
        return mk<TRUE>(efac);
      }

      if (n == 1) {
        ee = mk<PLUS>(ee, v);
      } else if (n == -1) {
        ee = mk<MINUS>(ee, v);
      } else {
        ee = mk<PLUS>(ee, mk<MULT>(exprFromNum(n, efac), v));
      }
    }

    number_t c = -cst.expression().constant();
    Expr cc = exprFromNum(c, efac);
    Expr res;
    if (cst.is_inequality()) {
      res = mk<LEQ>(ee, cc);
    } else if (cst.is_equality()) {
      res = mk<EQ>(ee, cc);
    } else {
      res = mk<NEQ>(ee, cc);
    }
    
    LOG("load-crab-details", llvm::errs() << *res << "\n";);	    
    return res;
  }

  Expr toExpr(lin_cst_sys_t csts, ExprFactory &efac, const DenseSet<const Value*> *live) {
    Expr e = mk<TRUE>(efac);

    // integers
    for (auto cst : csts) {
      e = boolop::land(e, toExpr(cst, efac, live));
    }

    // booleans
    for (auto p : bool_map) {
      auto b = p.second;
      if (!b.isUnknown()) {
        e = boolop::land(e, b.toExpr(efac, live));
      }
    }

    return e;
  }
};

/**
    Make consistent an Expr returned by LinConsToExpr with
    respect to semantics sem.

    We make the following assumptions:

    1) the input expression is defined over signed,
       infinite-precision integers, and

    2) it does not have any top-level logical operator.

    3) sem is either Ufo or Bv semantics. For new semantics, this
      code might need to be adapted.
 **/
class LinConToExprSem : public std::unary_function<Expr, VisitAction> {
public:
  using BvWidthMap = std::unordered_map<Expr, unsigned>;

private:
  OperationalSemantics &m_sem;
  OpSemContext &m_semCtx;
  BvWidthMap &m_width_map;

  class AdjustType : public std::unary_function<Expr, Expr> {
    ExprFactory &efac;
    BvWidthMap &width_map;

    bool isNumber(Expr e) {
      // LinConsToExpr only generates MPZ
      return isOpX<MPZ>(e);
    }

    expr::mpz_class getNumber(Expr e) {
      assert(isNumber(e));
      return getTerm<expr::mpz_class>(e);
    }

    bool isBv(Expr e) {
      return op::bv::is_bvnum(e) || bind::isConst<BVSORT>(e) ||
             /* we should see only these operators */
             isOpX<BADD>(e) || isOpX<BSUB>(e) || isOpX<BMUL>(e) ||
             isOpX<BSDIV>(e) || isOpX<BUDIV>(e) || isOpX<BSREM>(e) ||
             isOpX<BUREM>(e);
    }

    unsigned getBvWidth(Expr e) {
      if (bind::isConst<BVSORT>(e)) {
        Expr decl = bind::fname(e);
        Expr bvsort = decl->arg(1);
        return op::bv::width(bvsort);
      } else {
        return width_map[e];
      }
    }

  public:
    AdjustType(ExprFactory &_efac, BvWidthMap &map)
        : efac(_efac), width_map(map) {}

    // -- Convert an expression generated by LinConsToExpr to an
    // -- expression consistent with sem.
    //
    // Pre-condition: the children have been already processed.
    Expr operator()(Expr exp) {
      if (exp->arity() == 2) {

        // left and right have been already processed
        Expr left = exp->left();
        Expr right = exp->right();

        // Change number's types if the sibling is a bitvector operand
        if (isNumber(left) && (!isNumber(right) && isBv(right))) {
          unsigned width = getBvWidth(right);
          if (width == 0) {
            errs() << "ERROR: zero bitvector width in LinConsToExprSem\n";
            assert(false);
            return nullptr;
          }
          left = op::bv::bvnum(getNumber(left), width, efac);
          width_map[left] = width;
        } else if (isNumber(right) && (!isNumber(left) && isBv(left))) {
          unsigned width = getBvWidth(left);
          if (width == 0) {
            errs() << "ERROR: zero bitvector width in LinConsToExprSem\n";
            assert(false);
            return nullptr;
          }
          right = op::bv::bvnum(getNumber(right), width, efac);
          width_map[right] = width;
        }

        // Change operators if children are bitvector operands
        if (isBv(left) && isBv(right)) {

          if (isOpX<PLUS>(exp)) {
            exp = mk<BADD>(left, right);
          } else if (isOpX<MINUS>(exp)) {
            exp = mk<BSUB>(left, right);
          } else if (isOpX<MULT>(exp)) {
            exp = mk<BMUL>(left, right);
          } else if (isOpX<DIV>(exp) || isOpX<IDIV>(exp)) {
            exp = mk<BSDIV>(left, right);
          } else if (isOpX<LEQ>(exp)) {
            exp = mk<BSLE>(left, right);
          } else if (isOpX<GEQ>(exp)) {
            exp = mk<BSGE>(left, right);
          } else if (isOpX<LT>(exp)) {
            exp = mk<BSLT>(left, right);
          } else if (isOpX<GT>(exp)) {
            exp = mk<BSGT>(left, right);
          }

          unsigned left_width = getBvWidth(left);
          unsigned right_width = getBvWidth(right);
          if (left_width != right_width) {
            errs()
                << "ERROR: inconsistent bitvector width in LinConsToExprSem\n";
            assert(false);
            return nullptr;
          } else if (left_width == 0) {
            errs() << "ERROR: zero bitvector width in LinConsToExprSem\n";
            assert(false);
            return nullptr;
          } else {
            assert(left_width == right_width);
            assert(left_width != 0);
            width_map[exp] = left_width;
          }
        }
      }
      return exp;
    }
  };

public:
  LinConToExprSem(OperationalSemantics &sem, OpSemContext &semCtx, BvWidthMap &map)
    : m_sem(sem), m_semCtx(semCtx), m_width_map(map) {}

  VisitAction operator()(Expr exp) {
    if (isOpX<FAPP>(exp)) {      /* variable */
      Expr u = bind::fname(exp); // name of the app
      u = bind::fname(u);        // name of the fdecl
      assert(isOpX<VALUE>(u));
      const Value &v = *getTerm<const Value *>(u);
      Expr remap_exp = m_sem.mkSymbReg(v, m_semCtx);
      return VisitAction::changeTo(remap_exp);
    }

    // -- will descent the kids and then apply r

    std::shared_ptr<AdjustType> r(new AdjustType(exp->efac(), m_width_map));
    /** NumericOp */
    if (isOpX<PLUS>(exp) || isOpX<MINUS>(exp) || isOpX<MULT>(exp) ||
        isOpX<DIV>(exp) || isOpX<IDIV>(exp)) {
      return VisitAction::changeDoKidsRewrite(exp, r);
    }
    /** Comparison Op */
    else if (isOpX<EQ>(exp) || isOpX<NEQ>(exp) || isOpX<LEQ>(exp) ||
             isOpX<GEQ>(exp) || isOpX<LT>(exp) || isOpX<GT>(exp)) {
      return VisitAction::changeDoKidsRewrite(exp, r);
    }

    // -- descent kids
    return VisitAction::doKids();
  }
};// end LinConToExprSem
} // end namespace clam

namespace seahorn {
using namespace llvm;
using namespace clam;
using namespace expr;


LinConsToExpr::LinConsToExpr(const CfgBuilder *cfgBuilder, const llvm::Function &func)
    : m_impl(new LinConsToExprImpl(cfgBuilder, func)) {}

LinConsToExpr::~LinConsToExpr(){}

Expr LinConsToExpr::toExpr(const lin_cst_t &cst, ExprFactory &efac,
			   const DenseSet<const Value*> *live) {
  return m_impl->toExpr(cst, efac, live);
}

Expr LinConsToExpr::toExpr(const lin_cst_t &cst,
			   OperationalSemantics &sem, OpSemContext &semCtx,
			   const DenseSet<const Value*> *live) {
  Expr e = m_impl->toExpr(cst, sem.getExprFactory(), live);
  LinConToExprSem::BvWidthMap m;
  LinConToExprSem LCES(sem, semCtx, m);
  return dagVisit(LCES, e);
}

DisjunctiveLinConsToExpr::
DisjunctiveLinConsToExpr(const CfgBuilder *cfgBuilder, const llvm::Function &func)			 
  : m_e(new LinConsToExprImpl(cfgBuilder, func)) {}

DisjunctiveLinConsToExpr::~DisjunctiveLinConsToExpr(){}

Expr DisjunctiveLinConsToExpr::toExpr(const disj_lin_cst_sys_t &csts, ExprFactory &efac,
				      const DenseSet<const Value*> *live) {
  if (csts.is_false())
    return mk<FALSE>(efac);
  else if (csts.size() == 0)
    return mk<TRUE>(efac);
  else {
    assert(csts.size() > 0);
    Expr e = mk<FALSE>(efac);
    for (auto cst_sys : csts) {
      e = boolop::lor(e, m_e->toExpr(cst_sys, efac, live));
    }
    return e;
  }
}

LoadCrab::LoadCrab(const clam::ClamGlobalAnalysis &clam,
		   const clam::AnalysisParams &params,
		   HornifyModule &hm)
  : m_clam(clam), m_params(params), m_hm(hm) {}

Expr LoadCrab::CrabInvToExpr(llvm::BasicBlock &B, const CfgBuilder *cfgBuilder,
			     const DenseSet<const Value*> *live) {
  ExprFactory &efac = m_hm.getExprFactory();
  llvm::Function &fn = *(B.getParent());
  Expr e = mk<TRUE>(efac);
  
  llvm::Optional<clam_abstract_domain> absOpt = m_clam.getPre(&B, false);
  if (!absOpt.hasValue()) {
    return e;
  }

  auto abs = absOpt.getValue();
  if (m_params.dom.isDisjunctive()) {
    DisjunctiveLinConsToExpr t(cfgBuilder, fn);
    e = t.toExpr(abs.to_disjunctive_linear_constraint_system(), efac, live);
  } else {
    LinConsToExprImpl t(cfgBuilder, fn);
    e = t.toExpr(abs.to_linear_constraint_system(), efac, live);
  }

  if (live->empty() && (!isOpX<FALSE>(e))) {
    e = mk<TRUE>(efac);
  }

  return e;
}


bool LoadCrab::runOnModule(Module &M) {
  auto &db = m_hm.getHornClauseDB();
  auto const&cfgBuilderMan = m_clam.getCfgBuilderMan();
  
  for (auto &F : M) {
    if (F.empty()) {
      continue;
    }

    const CfgBuilder *cfgBuilder = cfgBuilderMan.getCfgBuilder(F);
    for (auto &BB : F) {
      // skip all basic blocks that HornifyModule does not know
      if (!m_hm.hasBbPredicate(BB)) {
	continue;
      }
      
      
      const ExprVector &liveE = m_hm.live(BB);
      DenseSet<const Value*> liveV;
      for (auto e : liveE) {
	Expr u = bind::fname(bind::fname(e));
	if (isOpX<VALUE>(u)) {
	  liveV.insert(getTerm<const Value *>(u));
	}
      }
      
      Expr exp = CrabInvToExpr(BB, cfgBuilder, &liveV);
      Expr pred = m_hm.bbPredicate(BB);
      LOG("crab", errs() << "Loading invariant " << *bind::fname(pred);
	  errs() << "("; for (auto v : liveE) errs() << *v << " ";
	  errs() << ")  " << *exp << "\n";);
      
      db.addInvariant(bind::fapp(pred, liveE), exp);
    }
  }
  return false;
}

bool LoadCrabPass::runOnModule(Module &M) {
  HornifyModule &hm = getAnalysis<HornifyModule>();
  ClamPass &clam = getAnalysis<ClamPass>();
  LoadCrab LC(clam.getClamGlobalAnalysis(), clam.getAnalysisParams(), hm);
  return LC.runOnModule(M);
}

void LoadCrabPass::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<HornifyModule>();
  AU.addRequired<ClamPass>();
}

} // end namespace seahorn
#endif
