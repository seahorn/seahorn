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

  bool isConst(Expr exp) {
    return bind::isBoolConst(exp) || bind::isIntConst(exp) ||
           bind::isRealConst(exp);
  }

  bool isValue(Expr exp) { return isOpX<TRUE>(exp) || isOpX<FALSE>(exp); }

  template <unsigned int N> bool numOfChildrenEq(Expr exp) {
    return exp->arity() == N;
  }

  template <unsigned int N> bool numOfChildrenGreaterEq(Expr exp) {
    return exp->arity() >= N;
  }

  bool isValidNumType(Expr exp) {
    if (exp != nullptr &&
        (isOp<INT_TY>(exp) || isOp<REAL_TY>(exp) || isOp<UNINT_TY>(exp)))
      return true;
    return false;
  }

  // ensures the expression has the correct number of children and all children
  // are the same and correct type
  Expr numTypeCheckChildren(Expr exp,
                            std::function<bool(Expr exp)> checkNumChildren) {
    if (!checkNumChildren(exp))
      return Expr();

    Expr type = m_cache.at(exp->first());
    auto isSameType = [this, type](Expr exp) {
      return type != nullptr && this->m_cache.at(exp) == type;
    };

    if (isValidNumType(type) &&
        std::all_of(exp->args_begin(), exp->args_end(), isSameType))
      return type;
    else
      return Expr();
  }

  Expr inferTypeNumUnary(Expr exp) {
    std::function<bool(Expr)> checkNumChildren =
        std::bind(&TCVR::numOfChildrenEq<1>, this, std::placeholders::_1);
    return numTypeCheckChildren(exp, checkNumChildren);
  }

  Expr inferTypeNumNary(Expr exp) {
    std::function<bool(Expr)> checkNumChildren = std::bind(
        &TCVR::numOfChildrenGreaterEq<2>, this, std::placeholders::_1);
    return numTypeCheckChildren(exp, checkNumChildren);
  }

  Expr inferTypeITE(Expr exp) {
    // ite(a,b,c) : a is bool type, b and c are the same type
    if (numOfChildrenEq<3>(exp) && isOp<BOOL_TY>(m_cache.at(exp->arg(0))) &&
        (m_cache.at(exp->arg(1)) == m_cache.at(exp->arg(2))))
      return sort::boolTy(exp->efac());
    else
      return Expr();
  }

  // ensures the expression has the correct number of children and all children
  // are bool types
  Expr boolCheckChildren(Expr exp,
                         std::function<bool(Expr exp)> checkNumChildren) {
    auto isBool = [this](Expr exp) {
      Expr type = this->m_cache.at(exp);

      return type != nullptr && isOp<BOOL_TY>(this->m_cache.at(exp));
    };

    if (checkNumChildren(exp) &&
        std::all_of(exp->args_begin(), exp->args_end(), isBool))
      return sort::boolTy(exp->efac());
    else
      return Expr();
  }

  Expr inferTypeBoolBinary(Expr exp) {
    std::function<bool(Expr)> checkNumChildren =
        std::bind(&TCVR::numOfChildrenEq<2>, this, std::placeholders::_1);
    return boolCheckChildren(exp, checkNumChildren);
  }

  Expr inferTypeBoolUnary(Expr exp) {
    std::function<bool(Expr)> checkNumChildren =
        std::bind(&TCVR::numOfChildrenEq<1>, this, std::placeholders::_1);
    return boolCheckChildren(exp, checkNumChildren);
  }

  Expr inferTypeBoolNary(Expr exp) {
    std::function<bool(Expr)> checkNumChildren = std::bind(
        &TCVR::numOfChildrenGreaterEq<2>, this, std::placeholders::_1);
    return boolCheckChildren(exp, checkNumChildren);
  }

  Expr inferType(Expr exp /*, TypeChecker & ty*/) {
    if (isOpX<TRUE>(exp) || isOpX<FALSE>(exp))
      return sort::boolTy(exp->efac());
    else if (bind::isBoolConst(exp))
      return sort::boolTy(exp->efac());
    else if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<XOR>(exp))
      return inferTypeBoolNary(exp);
    else if (isOpX<NEG>(exp))
      return inferTypeBoolUnary(exp);
    else if (isOpX<IMPL>(exp) || isOpX<IFF>(exp))
      return inferTypeBoolBinary(exp);
    else if (isOpX<ITE>(exp))
      return inferTypeITE(exp);

    else if (bind::isIntConst(exp))
      return sort::intTy(exp->efac());
    else if (bind::isRealConst(exp))
      return sort::realTy(exp->efac());
    else if (bind::isUnintConst(exp))
      return sort::unintTy(exp->efac());

    else if (isOpX<PLUS>(exp) || isOpX<MINUS>(exp) || isOpX<MULT>(exp) ||
             isOpX<DIV>(exp) || isOpX<IDIV>(exp) || isOpX<MOD>(exp) ||
             isOpX<REM>(exp) || isOpX<UN_MINUS>(exp))
      return inferTypeNumNary(exp);
    else if (isOpX<ABS>(exp))
      return inferTypeNumUnary(exp);

    return sort::anyTy(exp->efac());
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);

    Expr type = inferType(exp);

    m_cache.insert({exp, type});
    if (!type) {
      LOG("tc", llvm::errs()
                    << "Expression is not well-formed: " << *exp << "\n";);

      if (m_isWellFormed)
        m_errorExp = exp;

      m_isWellFormed = false;
    }

    return exp;
  }

public:
  TCVR() : m_isWellFormed(true) {}

  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("tc", llvm::errs() << "pre-visiting: " << *exp << "\n";);

    if (m_cache.count(exp) || !m_isWellFormed) {
      return false;
    } else if (isConst(exp) || isValue(exp)) {
      m_cache.insert({exp, inferType(exp)});
      return false;
    }

    return true;
  }

  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) { return e ? m_cache.at(e) : Expr(); }

  Expr getErrorExp() { return m_isWellFormed ? Expr() : m_errorExp; }
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

  Expr getErrorExp() { return m_rw->getErrorExp(); }
};
} // namespace

namespace expr {
class TypeChecker::Impl {
  Expr notWellFormedExp;

public:
  Expr typeOf(Expr e) {
    TCV _visitor;
    Expr v = visit(_visitor, e);
    notWellFormedExp = _visitor.getErrorExp();

    return _visitor.knownTypeOf(v);
  }

  Expr getErrorExp() { return notWellFormedExp; }
};

TypeChecker::TypeChecker() : m_impl(new TypeChecker::Impl()) {}
TypeChecker::~TypeChecker() { delete m_impl; }
Expr TypeChecker::typeOf(Expr e) { return m_impl->typeOf(e); }
Expr TypeChecker::getErrorExp() { // to be called after typeOf() or sortOf()

  return m_impl->getErrorExp();
}
} // namespace expr
