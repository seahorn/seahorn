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

  bool isConst (Expr exp) {
   return bind::isBoolConst(exp) || bind::isIntConst(exp);
  }

  bool isVar (Expr exp) {
   return bind::isBoolVar(exp) || bind::isIntVar(exp);
  }

  bool isValue (Expr exp) {
    return isOpX<TRUE>(exp) || isOpX<FALSE>(exp);
  }

  //returns true if children are of correct type
  bool checkChildren (Expr exp) {

    if (isOpX<ITE>(exp)) {
      //ite (a,b,c) : a is bool, b and c same type
      Expr c = expTypeStack.back(); 
      expTypeStack.pop_back();

      Expr b = expTypeStack.back(); 
      expTypeStack.pop_back();

      Expr a = expTypeStack.back(); 
      expTypeStack.pop_back();

      bool properTypes = (a == sort::boolTy (exp->efac())) && (b == c);
      return properTypes;
    }
    //default: check that chilren expressions are of the same types as the parent

    int numChildren = exp->arity();
    Expr parentType = bind::typeOf(exp);
    bool properTypes = true;

    for (int i = 0; i < numChildren; i ++) {
      properTypes = properTypes && expTypeStack.back () == parentType;
      expTypeStack.pop_back();
    }

    return properTypes;
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";); 

    if (!checkChildren(exp)) {
      LOG("tc", llvm::errs() << "improper types at:" << *exp  << "\n";);

      expTypeStack.push_back(Expr());
      return exp;
    }

      expTypeStack.push_back(bind::typeOf(exp));

    return exp;
  }

public:
  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("tc", llvm::errs() << "pre-visiting: " << *exp << "\n";);

    if (isConst(exp) || isVar(exp) || isValue(exp)) {
      expTypeStack.push_back(bind::typeOf(exp));
      return false;
    }

    return true;
  }
  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) {
    Expr type = expTypeStack.back();
      LOG("tc", llvm::errs() << "final stack size: " << expTypeStack.size() << "\n";);
//      assert(expTypeStack.size() == 1);
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
    if (m_rw->preVisit(exp)) 
      return VisitAction::changeDoKidsRewrite(exp, m_rw);
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
    Expr v = visit(_visitor, e);
    return _visitor.knownTypeOf(v);
  }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl()) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }

} // namespace expr
