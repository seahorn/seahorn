/*==-- Type Checker and Type Inference For Expressions --==*/
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/ExprErrBinder.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "llvm/Support/raw_ostream.h"

using namespace expr;
namespace {
// local code in this namespace
//==-- main implementation goes here --==//
class TCVR {

  ExprMap m_cache;

  bool m_isWellFormed;
  // records the last expression that caused an error.
  Expr m_errorExp;

  // keeps track of every error's first/bottom-most sub expression
  // for example, (bool && (int || int )) will map to (int || int)
  ExprMap m_errorMap;

  TypeChecker *const m_tc;

  // Keeps track of the expression that the typechecker is called with.
  // The expression is done traversing when it reaches the top most expression
  // so it can reset
  Expr m_topMost;

  void inferType(Expr exp) {
    Expr type = m_isWellFormed ? exp->op().inferType(exp, *m_tc)
                               : sort::errorTy(exp->efac());

    m_cache.insert({exp, type});

    if (isOp<ERROR_TY>(type)) {
      foundError(exp);
      m_errorMap.insert({exp, m_errorExp});
    } else if (isOp<ERRORBINDER>(type)) {
      ERR << "Error detail: " << *type << "\n";
      foundError(exp);
      m_errorMap.insert({exp, m_errorExp});
    }
  }

  void foundError(Expr exp) {
    ERR << "Expression is not well-formed: " << *exp << "\n";

    if (m_isWellFormed)
      m_errorExp = exp;

    m_isWellFormed = false;
  }

  void reset(Expr exp) {
    if (m_isWellFormed)
      m_errorExp = Expr();

    m_topMost = Expr();
    m_isWellFormed = true;
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);

    inferType(exp);

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

    if (!m_isWellFormed)
      return false;

    if (m_cache.count(exp)) {
      Expr type = m_cache.at(exp);

      if (isOp<ERROR_TY>(type) || isOp<ERRORBINDER>(type))
        foundError(m_errorMap.at(exp));

      return false;
    }

    if (exp->op().typeCheckTopDown()) {
      LOG("tc", llvm::errs() << "Top down: " << *exp << "\n";);
      inferType(exp);

      return false;
    }

    return true;
  }

  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) {
    Expr knownType = e ? m_cache.at(e) : Expr();

    if (e == m_topMost)
      reset(e); // done traversing entire expression

    LOG("tc",
        llvm::errs() << "known type of " << *e << "is " << *knownType << "\n";);
    return knownType;
  }

  Expr getErrorExp() { return m_errorExp; }
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
};
} // namespace

namespace expr {
class TypeChecker::Impl {
  TCV m_visitor;

public:
  Impl(TypeChecker *tc) : m_visitor(tc) {}

  Expr typeOf(Expr e) {
    Expr v = treeVisit(m_visitor, e);
    return m_visitor.knownTypeOf(v);
  }

  Expr getErrorExp() { return m_visitor.getErrorExp(); }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl(this)) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }
Expr TypeChecker::getErrorExp() { return m_impl->getErrorExp(); }

} // namespace expr
