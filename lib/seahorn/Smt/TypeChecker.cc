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
  ExprMap exprMap;

  bool isBool(Expr exp) {
    if (isOpX<TRUE>(exp) || isOpX<FALSE>(exp))
      return true;
    else if (bind::isBoolVar(exp) || bind::isBoolConst(exp))
      return true;
    else if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<XOR>(exp) ||
             isOpX<IMPL>(exp) || isOpX<ITE>(exp) || isOpX<IFF>(exp) ||
             isOpX<NEG>(exp))
      return true;

    return false;
  }

  Expr inferType(Expr exp /*,TypeChecker & ty*/) {
    if (isBool(exp))
      return sort::boolTy(exp->efac());
    else if (bind::isIntVar(exp) || bind::isIntConst(exp))
      return sort::intTy(exp->efac());

    return sort::anyTy(exp->efac());
  }

  bool isConst(Expr exp) {
    return bind::isBoolConst(exp) || bind::isIntConst(exp);
  }

  bool isVar(Expr exp) { return bind::isBoolVar(exp) || bind::isIntVar(exp); }

  bool isValue(Expr exp) { return isOpX<TRUE>(exp) || isOpX<FALSE>(exp); }

  // returns true if children are of correct type
  bool checkChildren(Expr exp) {

    if (isOpX<ITE>(exp)) {
      // ite (a,b,c) : a is bool, b and c same type
      bool aIsBool = exprMap[exp->arg(0)] == sort::boolTy(exp->efac());
      bool bCSame = exprMap[exp->arg(1)] == exprMap[exp->arg(2)];
      return aIsBool && bCSame;
    }

    // default: check that chilren expressions are of the same types as the
    // parent
    bool properTypes = true;
    Expr parentType = exprMap[exp];

    for (auto b = exp->args_begin(), e = exp->args_end(); b != e && properTypes;
         ++b) {
      properTypes = exprMap[*b] == parentType;
    }

    return properTypes;
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);

    exprMap[exp] = inferType(exp);

    if (!checkChildren(exp)) {
      LOG("tc", llvm::errs() << "improper types at:" << *exp << "\n";);
      exprMap[exp] = Expr();
    }

    return exp;
  }

public:
  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("tc", llvm::errs() << "pre-visiting: " << *exp << "\n";);

    if (exprMap[exp]) {
      return false;
    } else if (isConst(exp) || isVar(exp) || isValue(exp)) {
      exprMap[exp] = inferType(exp);
      return false;
    }

    return true;
  }

  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) { return e ? exprMap[e] : Expr(); }
};

//==-- Adapts visitor for pre- and post- traversal --==/
class TCV : public std::unary_function<Expr, VisitAction> {
  std::shared_ptr<TCVR> m_rw;

public:
  TCV() : m_rw(std::make_shared<TCVR>()) {}
  VisitAction operator()(Expr exp) {
    if (m_rw->preVisit(exp))
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    else
      return VisitAction::skipKids();
  }

  /// Returns known type of \ e
  /// Should be called after visiting the expression to compute its type
  Expr knownTypeOf(Expr e) { return m_rw->knownTypeOf(e); }
};
} // namespace

namespace expr {
class TypeChecker::Impl {
public:
  Expr typeOf(Expr e) {
    TCV _visitor;
    Expr v = dagVisit(_visitor, e);
    return _visitor.knownTypeOf(v);
  }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl()) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }

} // namespace expr
