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

  bool isConst(Expr exp) {
    return bind::isBoolConst(exp) || bind::isIntConst(exp);
  }

  bool isVar(Expr exp) { return bind::isBoolVar(exp) || bind::isIntVar(exp); }

  bool isValue(Expr exp) { return isOpX<TRUE>(exp) || isOpX<FALSE>(exp); }

  Expr inferTypeITE(Expr exp) {
    Expr boolSort = sort::boolTy(exp->efac());

    // ite(a,b,c) : a is bool type, b and c are the same type
    if (exp->arity() == 3 && m_cache.at(exp->arg(0)) == boolSort &&
        (m_cache.at(exp->arg(1)) == m_cache.at(exp->arg(2))))
      return boolSort;
    else
      return Expr();
  }

  // ensures the expression has the correct number of children and all children
  // are bool types
  Expr boolCheckChildren(Expr exp, bool (*checkNumChildren)(int)) {
    auto isBool = [this](Expr exp) {
      return this->m_cache.at(exp) == sort::boolTy(exp->efac());
    };

    if (checkNumChildren(exp->arity()) &&
        std::all_of(exp->args_begin(), exp->args_end(), isBool))
      return sort::boolTy(exp->efac());
    else
      return Expr();
  }

  Expr inferTypeIMP(Expr exp) {
    auto checkNumChildren = [](int numChildren) -> bool {
      return numChildren == 2;
    };
    return boolCheckChildren(exp, checkNumChildren);
  }

  Expr inferTypeNEG(Expr exp) {
    auto checkNumChildren = [](int numChildren) -> bool {
      return numChildren == 1;
    };
    return boolCheckChildren(exp, checkNumChildren);
  }

  Expr inferTypeBoolMulti(Expr exp) {
    auto checkNumChildren = [](int numChildren) -> bool {
      return numChildren >= 2;
    };
    return boolCheckChildren(exp, checkNumChildren);
  }

  Expr inferType(Expr exp /*,TypeChecker & ty*/) {
    if (isOpX<TRUE>(exp) || isOpX<FALSE>(exp))
      return sort::boolTy(exp->efac());
    else if (bind::isBoolVar(exp) || bind::isBoolConst(exp))
      return sort::boolTy(exp->efac());
    else if (isOpX<AND>(exp) || isOpX<OR>(exp) || isOpX<XOR>(exp))
      return inferTypeBoolMulti(exp);
    else if (isOpX<NEG>(exp))
      return inferTypeNEG(exp);
    else if (isOpX<IMPL>(exp) || isOpX<IFF>(exp))
      return inferTypeIMP(exp);
    else if (isOpX<ITE>(exp))
      return inferTypeITE(exp);
    else if (bind::isIntVar(exp) || bind::isIntConst(exp))
      return sort::intTy(exp->efac());

    return sort::boolTy(exp->efac());
  }

  /// Called after children have been visited
  Expr postVisit(Expr exp) {
    LOG("tc", llvm::errs() << "post visiting expression: " << *exp << "\n";);

    Expr type = inferType(exp);

    m_cache.insert({exp, type});
    if (!type)
      LOG("tc", llvm::errs()
                    << "Expression is not well-formed: " << *exp << "\n";);

    return exp;
  }

public:
  /// Called before children are visited
  /// Returns false to skip visiting children
  bool preVisit(Expr exp) {
    LOG("tc", llvm::errs() << "pre-visiting: " << *exp << "\n";);

    if (m_cache.count(exp)) {
      return false;
    } else if (isConst(exp) || isVar(exp) || isValue(exp)) {
      m_cache.insert({exp, inferType(exp)});
      return false;
    }

    return true;
  }

  Expr operator()(Expr exp) { return postVisit(exp); }

  Expr knownTypeOf(Expr e) { return e ? m_cache.at(e) : Expr(); }
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
