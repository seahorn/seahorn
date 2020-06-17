/*==-- Type Checker and Type Inference For Expressions --==*/
#include "seahorn/Expr/TypeChecker.hh"
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
  Expr m_errorExp;

  // keeps track of every error's first/bottom-most sub expression
  // for example, (bool && (int || int )) will map to (int || int)
  ExprMap m_errorMap;

  TypeCheckerHelper *const m_helper;

  // Keeps track of the expression that the typechecker is called with.
  // The expression is done traversing when it reaches the top most expression
  // so it can reset
  Expr m_topMost;

  // Keeps track of all the bound variables that an expression uses
  std::map<Expr, ExprSet> m_boundVarMap;
  ExprSet m_binders;

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

  // merges all of the expressions bound vars into one set and maps the
  // expression to this set
  void mapBoundVarsToParent(Expr exp) {

    // if the expression is a binder, then its bound variables will not be
    // within its parents scope, so don't map them
    if (m_binders.count(exp))
      return;

    ExprSet set;

    // Get a copy of all children sets merged into one
    for (auto b = exp->args_begin(), e = exp->args_end(); b != e; b++) {
      if (m_boundVarMap.count(
              *b)) { // if the child expression has any bound variables
        set.insert(m_boundVarMap.at(*b).begin(), m_boundVarMap.at(*b).end());
      }
    }

    if (!set.empty())
      m_boundVarMap.insert({exp, set});
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);

    Expr type = m_isWellFormed ? exp->op().inferType(exp, *m_helper)
                               : sort::errorTy(exp->efac());

    m_cache.insert({exp, type});

    if (isOp<ERROR_TY>(type)) {
      foundError(exp);
      m_errorMap.insert({exp, m_errorExp});
    } else {
      mapBoundVarsToParent(exp);
    }

    return exp;
  }

public:
  TCVR(TypeCheckerHelper *helper)
      : m_isWellFormed(true), m_helper(helper), m_topMost(Expr()) {}

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

      if (isOp<ERROR_TY>(type))
        foundError(m_errorMap.at(exp));

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

  void mapBoundVar(Expr bVar) {
    ExprSet set;
    set.insert(bVar);
    m_boundVarMap.insert({bVar, set});
  }

  ExprSet getBoundVars(Expr exp) {
    ExprSet emptySet;
    return m_boundVarMap.count(exp) ? m_boundVarMap.at(exp) : emptySet;
  }

  void mapBinder(Expr binder) { m_binders.insert(binder); }
};

//==-- Adapts visitor for pre- and post- traversal --==/
class TCV : public std::unary_function<Expr, VisitAction> {
  std::shared_ptr<TCVR> m_rw;

public:
  TCV(TypeCheckerHelper *helper) : m_rw(std::make_shared<TCVR>(helper)) {}
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

  void mapBoundVar(Expr bVar) { m_rw->mapBoundVar(bVar); }

  ExprSet getBoundVars(Expr exp) { return m_rw->getBoundVars(exp); }

  void mapBinder(Expr binder) { m_rw->mapBinder(binder); }
};
} // namespace

namespace expr {
class TypeCheckerHelper::Impl {
  TCV m_visitor;

public:
  Impl(TypeCheckerHelper *helper) : m_visitor(helper) {}

  Expr typeOf(Expr e) {
    Expr v = visit(m_visitor, e);

    return m_visitor.knownTypeOf(v);
  }

  Expr getErrorExp() { return m_visitor.getErrorExp(); }

  void mapBoundVar(Expr bVar) { m_visitor.mapBoundVar(bVar); }

  ExprSet getBoundVars(Expr exp) { return m_visitor.getBoundVars(exp); }

  void mapBinder(Expr binder) { m_visitor.mapBinder(binder); }
};

TypeCheckerHelper::TypeCheckerHelper()
    : m_impl(new TypeCheckerHelper::Impl(this)) {}
TypeCheckerHelper::~TypeCheckerHelper() { delete m_impl; }
Expr TypeCheckerHelper::typeOf(Expr e) { return m_impl->typeOf(e); }
Expr TypeCheckerHelper::getErrorExp() { return m_impl->getErrorExp(); }
void TypeCheckerHelper::mapBoundVar(Expr bVar) { m_impl->mapBoundVar(bVar); }
ExprSet TypeCheckerHelper::getBoundVars(Expr exp) {
  return m_impl->getBoundVars(exp);
}
void TypeCheckerHelper::mapBinder(Expr binder) { m_impl->mapBinder(binder); }

TypeChecker::TypeChecker() {}
Expr TypeChecker::typeOf(Expr e) { return m_helper.typeOf(e); }

// to be called after typeOf() or sortOf()
Expr TypeChecker::getErrorExp() { return m_helper.getErrorExp(); }

} // namespace expr
