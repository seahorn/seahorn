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

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);
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
    // if e is non null, return ANY type, ow return nil expression
    return e ? sort::anyTy(e->efac()) : Expr();
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
    visit(_visitor, e);
    return _visitor.knownTypeOf(e);
  }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl()) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }

} // namespace expr
