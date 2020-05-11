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
  ExprVector expTypeStack;

  //TODO
  bool isInt (Expr exp, bool & properTypes) {
    if (bind::isIntConst(exp)) {
      return true;
    }
    return false;
  }

  bool isBool (Expr exp, bool & properTypes) {
    properTypes = true;
    Expr boolSort = sort::boolTy(exp->efac());

    if (isOpX <AND> (exp) || isOpX <OR> (exp) || isOpX <XOR> (exp)) {
       int numChildren = exp->arity();

      for (int i = 0; i < numChildren; i ++) {
        properTypes = properTypes && expTypeStack.back () == boolSort;
        expTypeStack.pop_back();
      }

      return true;
    }
    else if (isOpX <IMPL> (exp) || isOpX <IFF> (exp)) {
      properTypes = expTypeStack.back () == boolSort;
      expTypeStack.pop_back();
      properTypes = properTypes && expTypeStack.back () == boolSort;
      expTypeStack.pop_back();

      return true;
    }
    else if (isOpX <NEG> (exp)) {
      properTypes = expTypeStack.back() == boolSort;
      expTypeStack.pop_back();

      return true;
    }
    else if (isOpX<TRUE>(exp) || isOpX<FALSE>(exp) || bind::isBoolVar(exp) || bind::isBoolConst(exp)) {
      return true;
    }

    return false;
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);
    Expr type = nullptr;

    bool properTypes = true;

    if (isBool(exp, properTypes)) {
      type = sort::boolTy(exp->efac());
    }
    else if (isInt(exp, properTypes)) {
      type = sort::intTy(exp->efac());
    }
    else {
      LOG("tc", llvm::errs() << "unknown type" << *exp << "\n");
      type = Expr();
    }

    if (!properTypes){
      LOG("tc", llvm::errs() << "improper types at:" << *exp << "\n";);
      type = Expr();
      expTypeStack.push_back(type);
      return type;
    }

  //  if (type) {
      expTypeStack.push_back(type);
  // }

    return exp;
  }

public:
  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("tc", llvm::errs() << "pre-visiting: " << *exp << "\n";);
    return true;
  }
  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) {
    LOG("tc", llvm::errs() << "Request type of: " << *e << "\n";);

    Expr type = expTypeStack.back();
    expTypeStack.clear();

    return type;
  }
};

//==-- Adapts visitor for pre- and post- traversal --==/
class TCV : public std::unary_function<Expr, VisitAction> {
  std::shared_ptr<TCVR> m_rw;

public:
  TCV() : m_rw(std::make_shared<TCVR>()) {}
  VisitAction operator()(Expr exp) {
    if (m_rw->preVisit(exp)) {
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
    }
    else
      return VisitAction::skipKids();
  }

  /// Returns known type of \ e
  /// Should be called after visiting the expression to compute its type
  Expr knownTypeOf(Expr e) {
    return m_rw->knownTypeOf(e);
    ;
  }
};
} // namespace

namespace expr {
class TypeChecker::Impl {
public:
  Expr typeOf(Expr e) {
    TCV _visitor;
    visit(_visitor, e);
    return _visitor.knownTypeOf(e);
  }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl()) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }

} // namespace expr
