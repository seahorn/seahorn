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
  bool m_isWellFormed = true;
  Expr m_errorExp;
  TypeChecker *m_tc;

  bool isConst(Expr exp) {
    return bind::isBoolConst(exp) || bind::isIntConst(exp) ||
           bind::isRealConst(exp);
  }

  bool isValue(Expr exp) { return isOpX<TRUE>(exp) || isOpX<FALSE>(exp); }

  Expr inferType(Expr exp , TypeChecker & tc) {
    if (isOpX<TRUE>(exp) || isOpX<FALSE>(exp))
      return sort::boolTy(exp->efac());
    else if (bind::isBoolConst(exp))
      return sort::boolTy(exp->efac());
    // else if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<XOR>(exp))
    //   return inferTypeBoolNary(exp);
    // else if (isOpX<NEG>(exp))
    //   return inferTypeBoolUnary(exp);
    // else if (isOpX<IMPL>(exp) || isOpX<IFF>(exp))
    //   return inferTypeBoolBinary(exp);
    // else if (isOpX<ITE>(exp))
    //   return inferTypeITE(exp);

    else if (bind::isIntConst(exp))
      return sort::intTy(exp->efac());
    else if (bind::isRealConst(exp))
      return sort::realTy(exp->efac());
    else if (bind::isUnintConst(exp))
      return sort::unintTy(exp->efac());

    // else if (isOpX<PLUS>(exp) || isOpX<MINUS>(exp) || isOpX<MULT>(exp) ||
    //          isOpX<DIV>(exp) || isOpX<IDIV>(exp) || isOpX<MOD>(exp) ||
    //          isOpX<REM>(exp) || isOpX<UN_MINUS>(exp))
    //   return inferTypeNumNary(exp);
    // else if (isOpX<ABS>(exp))
    //   return inferTypeNumUnary(exp);

    return exp->inferType(exp, tc);
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);

    Expr type = inferType(exp, *m_tc);

    m_cache.insert({exp, type});
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
  TCVR(TypeChecker *tc) : m_isWellFormed(true), m_tc(tc) {}

  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("tc", llvm::errs() << "pre-visiting: " << *exp << "\n";);

    if (m_cache.count(exp) || !m_isWellFormed) {
      return false;
    } else if (isConst(exp) || isValue(exp)) {
      m_cache.insert({exp, inferType(exp, *m_tc)});
      return false;
    }
    return true;
  }

  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) { 
    if (m_isWellFormed) {
      m_errorExp = Expr();
    }
    m_isWellFormed = true;

    return e ? m_cache.at(e) : Expr(); 
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
  Impl (TypeChecker *tc) : m_visitor(tc) {}

  Expr typeOf(Expr e) {
    Expr v = visit(m_visitor, e);

    return m_visitor.knownTypeOf(v);
  }

  Expr getErrorExp() { return m_visitor.getErrorExp(); }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl(this)) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }
Expr TypeChecker::getErrorExp() { // to be called after typeOf() or sortOf()
  return m_impl->getErrorExp();
}

namespace op{
namespace typeCheck {
    inline Expr ANY::inferType(Expr exp, TypeChecker &tc) {
      std::cout<<""<<std::endl;
      return sort::anyTy(exp->efac());
    }
  } // namespace typeCheck
} // namespace op
} // namespace expr
