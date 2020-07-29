#include "seahorn/LoadCrab.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/config.h"

#include "llvm/Support/raw_ostream.h"

namespace seahorn {
char LoadCrab::ID = 0;
llvm::Pass *createLoadCrabPass() { return new LoadCrab(); }
} // namespace seahorn

#ifndef HAVE_CLAM
/// Dummy implementation when Crab is not compiled in
namespace seahorn {
void LoadCrab::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool LoadCrab::runOnModule(llvm::Module &M) {
  llvm::errs()
      << "WARNING: Not loading invariants. Compiled without Crab support.\n";
  return false;
}
bool LoadCrab::runOnFunction(llvm::Function &F) { return false; }
} // namespace seahorn
#else
/// Real implementation starts here
#include "llvm/ADT/DenseSet.h"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprLlvm.hh"

#include "seahorn/HornifyModule.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "clam/CfgBuilder.hh"
#include "clam/Clam.hh"
#include "clam/HeapAbstraction.hh"

#include "boost/unordered_map.hpp"

namespace clam {

using namespace llvm;
using namespace expr;
using namespace seahorn;

// Conversion from linear constraints to Expr.
//
// A linear constraint is precisely translated only if all its
// variables can be mapped to llvm Value. Otherwise, it is
// translated to true. For instance, Crab generates shadow variables
// representing DSA nodes that are not translated with the exception
// of global singletons.
class LinConsToExprImpl {
public:
  // Crab does not distinguish between bools and the rest of
  // integers but SeaHorn does.

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

    Expr toExpr(ExprFactory &efac) const {
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
  typedef DenseMap<const Value *, BoolCst> bool_map_t;

  HeapAbstraction &m_heap_abs;
  const llvm::Function &m_func;
  const ExprVector &m_live;
  DenseSet<const Value *> m_live_values; // for fast queries
  bool_map_t bool_map;

  // Defined only for z_number
  Expr exprFromNum(ikos::z_number n, ExprFactory &efac) {
    const expr::mpz_class z(n.get_mpz_t());
    return mkTerm(z, efac);
  }

  Expr exprFromIntVar(varname_t v, ExprFactory &efac) {
    if (!(v.get())) {
      // Skip for now crab shadow variables.

      // TODO: v.get() method only returns a non-null value if v
      // contains a const Value*. Otherwise, it means that v refers
      // to a shadow variable which is not currently translated.
      return nullptr;
    }
    const Value *V = *(v.get());
    if (const Value *Gv =
            m_heap_abs.getRegion(m_func, nullptr, const_cast<Value *>(V))
                .getSingleton()) {
      /// -- The crab variable v corresponds to a global singleton
      ///    cell so we can grab a llvm Value from it. We search for
      ///    the seahorn shadow variable that matches it.
      for (auto l : m_live) {
        Expr u = bind::fname(bind::fname(l));
        if (isOpX<VALUE>(u)) {
          // u is a constant
          const Value *U = getTerm<const Value *>(u);
          const Value *Scalar;
          if (shadow_dsa::isShadowMem(*U, &Scalar)) {
            if (Scalar == Gv) {
              return bind::intConst(mkTerm<const Value *>(U, efac));
            }
          }
        } else if (isOpX<op::SELECT>(u)) {
          // u is a constant with name v[scalar]
          Expr idx = u->right();
          if (isOpX<VALUE>(idx)) {
            const Value *Idx = getTerm<const Value *>(idx);
            if (Idx == Gv)
              return bind::intConst(u);
          }
        }
      }
      // We could not translate the global singleton cell
      return nullptr;
    } else {
      // -- If here then v can be mapped directly to a llvm value
      //    after we check v is live. This is needed because we do
      //    not currently project the abstract domain onto the live
      //    variables before translation.
      if (m_live_values.count(V) > 0) {
        return bind::intConst(mkTerm<const Value *>(V, efac));
      } else {
        return nullptr;
      }
    }
  }

public:
  LinConsToExprImpl(HeapAbstraction &heap_abs, const llvm::Function &f,
                    const ExprVector &live)
      : m_heap_abs(heap_abs), m_func(f), m_live(live) {
    for (auto v : m_live) {
      Expr u = bind::fname(bind::fname(v));
      if (isOpX<VALUE>(u))
        m_live_values.insert(getTerm<const Value *>(u));
    }
  }

  Expr toExpr(const lin_cst_t &cst, ExprFactory &efac) {
    if (cst.is_tautology())
      return mk<TRUE>(efac);

    if (cst.is_contradiction())
      return mk<FALSE>(efac);

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

      return mk<TRUE>(efac); // we ignore cst for now
    }

    // integers
    auto e = cst.expression() - cst.expression().constant();
    Expr ee = exprFromNum(number_t("0"), efac);
    for (auto t : e) {
      number_t n = t.first;
      if (n == 0)
        continue;

      Expr v = exprFromIntVar(t.second.name(), efac);
      if (!v) {
        // We could not translate Crab variable.
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
    if (cst.is_inequality())
      return mk<LEQ>(ee, cc);
    else if (cst.is_equality())
      return mk<EQ>(ee, cc);
    else
      return mk<NEQ>(ee, cc);
  }

  Expr toExpr(lin_cst_sys_t csts, ExprFactory &efac) {
    Expr e = mk<TRUE>(efac);

    // integers
    for (auto cst : csts) {
      e = boolop::land(e, toExpr(cst, efac));
    }

    // booleans
    for (auto p : bool_map) {
      auto b = p.second;
      if (!b.isUnknown()) {
        e = boolop::land(e, b.toExpr(efac));
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
  typedef boost::unordered_map<Expr, unsigned> BvWidthMap;

private:
  LegacyOperationalSemantics &m_sem;
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
  LinConToExprSem(LegacyOperationalSemantics &sem, BvWidthMap &map)
      : m_sem(sem), m_width_map(map) {}

  VisitAction operator()(Expr exp) {
    if (isOpX<FAPP>(exp)) {      /* variable */
      Expr u = bind::fname(exp); // name of the app
      u = bind::fname(u);        // name of the fdecl
      assert(isOpX<VALUE>(u));
      const Value &v = *getTerm<const Value *>(u);
      Expr remap_exp = m_sem.symb(v);
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
};

class DisjunctiveLinConsToExpr {
  LinConsToExprImpl m_t;

public:
  DisjunctiveLinConsToExpr(HeapAbstraction &heap_abs, const llvm::Function &f,
                           const ExprVector &live)
      : m_t(heap_abs, f, live) {}

  Expr toExpr(const disj_lin_cst_sys_t &csts, ExprFactory &efac) {
    if (csts.is_false())
      return mk<FALSE>(efac);
    else if (csts.size() == 0)
      return mk<TRUE>(efac);
    else {
      assert(csts.size() > 0);
      Expr e = mk<FALSE>(efac);
      for (auto cst : csts) {
        e = boolop::lor(e, m_t.toExpr(cst, efac));
      }
      return e;
    }
  }
};

} // end namespace clam

namespace seahorn {
using namespace llvm;
using namespace clam;
using namespace expr;

#if 0
// Translate a range of Expr variables to Crab variables but only
// those that can be mapped to llvm value.

// UPDATE: we are creating variables without types. This might cause
// problems.
template <typename Range>
static std::vector<clam::var_t> ExprVecToCrab(const Range &live, ClamPass *clam) {
  std::vector<clam::var_t> res;
  for (auto l : live) {
    Expr u = bind::fname(bind::fname(l));
    if (isOpX<VALUE>(u)) {
      const Value *v = getTerm<const Value *>(u);
      if (isa<GlobalVariable>(v))
        continue;

      res.push_back(
	  clam::var_t(clam->getCfgBuilderMan().
		      getVarFactory()[v], crab::UNK_TYPE, 0));
    }
  }
  return res;
}
#endif

LinConsToExpr::LinConsToExpr(HeapAbstraction &heap, const llvm::Function &f,
                             const ExprVector &live)
    : m_impl(new LinConsToExprImpl(heap, f, live)) {}

LinConsToExpr::~LinConsToExpr() { delete m_impl; }

Expr LinConsToExpr::toExpr(lin_cst_t cst, ExprFactory &efac) {
  return m_impl->toExpr(cst, efac);
}

Expr LinConsToExpr::toExpr(lin_cst_t cst, LegacyOperationalSemantics &sem) {
  Expr e = m_impl->toExpr(cst, sem.getExprFactory());
  LinConToExprSem::BvWidthMap m;
  LinConToExprSem LCES(sem, m);
  return dagVisit(LCES, e);
}

Expr CrabInvToExpr(llvm::BasicBlock *B, ClamPass *clam, const ExprVector &live,
                   EZ3 &zctx, ExprFactory &efac) {

  Expr e = mk<TRUE>(efac);
  llvm::Optional<clam_abstract_domain> absOpt = clam->getPre(B);
  if (!absOpt.hasValue()) {
    return e;
  }

  auto abs = absOpt.getValue();
  const AnalysisParams &clamParams = clam->getAnalysisParams();

// Here we do project onto live variables before translation
#if 0
  std::vector<clam::var_t> vars = ExprVecToCrab(live, clam);
  abs.project(vars);
#endif

  if (clamParams.dom.isDisjunctive()) {
    DisjunctiveLinConsToExpr t(clam->getCfgBuilderMan().getHeapAbstraction(),
                               *(B->getParent()), live);
    e = t.toExpr(abs.to_disjunctive_linear_constraint_system(), efac);
  } else {
    LinConsToExprImpl t(clam->getCfgBuilderMan().getHeapAbstraction(),
                        *(B->getParent()), live);
    e = t.toExpr(abs.to_linear_constraint_system(), efac);
  }

  if ((std::distance(live.begin(), live.end()) == 0) && (!isOpX<FALSE>(e))) {
    e = mk<TRUE>(efac);
  }

  return e;
}

bool LoadCrab::runOnModule(Module &M) {
  for (auto &F : M) {
    runOnFunction(F);
  }
  return false;
}

bool LoadCrab::runOnFunction(Function &F) {
  HornifyModule &hm = getAnalysis<HornifyModule>();
  ClamPass &clam = getAnalysis<ClamPass>();

  auto &db = hm.getHornClauseDB();

  for (auto &BB : F) {
    // skip all basic blocks that HornifyModule does not know
    if (!hm.hasBbPredicate(BB))
      continue;

    const ExprVector &live = hm.live(BB);

    Expr exp =
        CrabInvToExpr(&BB, &clam, live, hm.getZContext(), hm.getExprFactory());

    Expr pred = hm.bbPredicate(BB);

    LOG("crab", errs() << "Loading invariant " << *bind::fname(pred);
        errs() << "("; for (auto v
                            : live) errs()
                       << *v << " ";
        errs() << ")  " << *exp << "\n";);

    db.addInvariant(bind::fapp(pred, live), exp);
  }
  return false;
}

void LoadCrab::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<HornifyModule>();
  AU.addRequired<ClamPass>();
}

} // end namespace seahorn
#endif
