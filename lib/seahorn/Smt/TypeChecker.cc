/*==-- Type Checker and Type Inference For Expressions --==*/
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Support/SeaDebug.h"
#include "llvm/Support/raw_ostream.h"

using namespace expr;
namespace {
// local code in this namespace
//==-- main implementation goes here --==//
class TCVR {

  ExprMap m_cache;
  std::map<Expr, ExprSet> m_endExpr;

  bool m_isWellFormed;
  Expr m_errorExp;

  TypeChecker *const m_tc;
  Expr m_topMost;

  void reset(Expr exp) {
    if (m_isWellFormed)
      m_errorExp = Expr();

    m_topMost = Expr();
    m_isWellFormed = true;
    m_cache.clear();
  }

  bool isConst(Expr exp) {
    return bind::isBoolConst(exp) || bind::isIntConst(exp) ||
           bind::isRealConst(exp) || bind::isUnintConst(exp) ||
           bind::isArrayConst(exp) || bind::isStructConst(exp) ||
           bv::isBvConst(exp);
  }

  bool isValue(Expr exp) { return isOpX<TRUE>(exp) || isOpX<FALSE>(exp); }

  bool isSimpleType(Expr exp) {
    return isConst(exp) || isValue(exp) || bv::is_bvnum(exp);
  }

  void mapEndTypes(Expr exp) {
    ExprSet set;

    if (exp->arity() == 0) {
      set.insert(exp);
    }

    std::for_each(exp->args_begin(), exp->args_end(), [this, &set](Expr child) {
      if (this->m_endExpr.count(child)) {
        ExprSet childSet = this->m_endExpr.at(child);
        set.insert(childSet.begin(), childSet.end());
      }
    });

    m_endExpr.insert({exp, set});
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);

    Expr type = exp->inferType(exp, *m_tc);

    m_cache.insert({exp, type});
    mapEndTypes(exp);

    if (isOp<ERROR_TY>(type)) {
      LOG("tc", llvm::errs()
                    << "Expression is not well-formed: " << *exp << "\n";);

      if (m_isWellFormed)
        m_errorExp = exp;

      m_isWellFormed = false;
    }

    return exp;
  }

public:
  TCVR(TypeChecker *tc) : m_isWellFormed(true), m_tc(tc), m_topMost(Expr()) {}

  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("tc", llvm::errs() << "pre-visiting: " << *exp << "\n";);

    if (!m_topMost) {
      LOG("tc", llvm::errs() << "top most expression: " << *exp << "\n";);
      m_topMost = exp;
    }

    if (m_cache.count(exp) || !m_isWellFormed) {
      return false;
    } else if (isSimpleType(exp)) {
      m_cache.insert({exp, exp->inferType(exp, *m_tc)});

      ExprSet set;
      set.insert(exp);
      m_endExpr.insert({exp, set});
      return false;
    }
    return true;
  }

  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) {
    Expr knownType = e ? m_cache.at(e) : Expr();

    if (e == m_topMost) // done traversing entire expression
      reset(e);

    return knownType;
  }

  Expr getErrorExp() { return m_errorExp; }

  ExprSet getEndExps(Expr e) { return m_endExpr.at(e); }
};

//==-- Adapts visitor for pre- and post- traversal --==/
class TCV : public std::unary_function<Expr, VisitAction> {
  std::shared_ptr<TCVR> m_rw;

public:
  TCV(TypeChecker *tc) : m_rw(std::make_shared<TCVR>(tc)) {}
  VisitAction operator()(Expr exp) {
    if (m_rw->preVisit(exp))
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    else
      return VisitAction::skipKids();
  }

  /// Returns known type of \ e
  /// Should be called after visiting the expression to compute its type
  Expr knownTypeOf(Expr e) { return m_rw->knownTypeOf(e); }

  Expr getErrorExp() { return m_rw->getErrorExp(); }

  ExprSet getEndExps(Expr e) { return m_rw->getEndExps(e); }
};
} // namespace

namespace expr {
class TypeChecker::Impl {
  TCV m_visitor;

public:
  Impl(TypeChecker *tc) : m_visitor(tc) {}

  Expr typeOf(Expr e) {
    Expr v = visit(m_visitor, e);

    return m_visitor.knownTypeOf(v);
  }

  Expr getErrorExp() { return m_visitor.getErrorExp(); }

  ExprSet getEndExps(Expr e) { return m_visitor.getEndExps(e); }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl(this)) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }

// to be called after typeOf() or sortOf()
Expr TypeChecker::getErrorExp() { return m_impl->getErrorExp(); }

// to be called after typeOf() or sortOf()
ExprSet TypeChecker::getEndExps(Expr e) { return m_impl->getEndExps(e); }
} // namespace expr
