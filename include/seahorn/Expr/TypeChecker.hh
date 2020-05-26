#pragma once
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpSort.hh"

namespace expr {
class TypeChecker {
  class Impl;
  Impl *m_impl;

public:
  TypeChecker();
  ~TypeChecker();
  Expr sortOf(Expr e) { return this->typeOf(e); }
  Expr typeOf(Expr e);
  Expr getErrorExp(); // to be called after typeOf() or sortOf()
};

namespace op {
namespace typeCheck {
enum Comparison {
  Equal,
  GreaterEqual
};

template <Comparison compareType, unsigned int numChildren>
static inline bool checkNumChildren(Expr exp) {
  if (compareType == Equal) 
    return exp->arity() == numChildren;
  else if (compareType == GreaterEqual)
    return exp->arity() >= numChildren;

  return false;
}

// returns true if all children share the same type
static inline bool sameType(Expr exp, TypeChecker &tc) {
  Expr type = tc.typeOf(exp->first());

  auto isSameType = [&tc, &type](Expr exp) {
    return type != nullptr && tc.typeOf(exp) == type;
  };
  return std::all_of(exp->args_begin(), exp->args_end(), isSameType);
}

// return true if the expression is of type T
template <typename T>
static inline bool correctType(Expr exp, TypeChecker &tc) {
  return isOp<T>(tc.typeOf(exp));
}

template <> static inline bool correctType<ANY_TY>(Expr exp, TypeChecker &tc) {
  return true;
}

// returns true if the type of the expression matches any of the passed types
template <typename T, typename T2, typename... types>
static inline bool correctType(Expr exp, TypeChecker &tc) {
  if (isOp<T>(tc.typeOf(exp)))
    return true;

  return correctType<T2, types...>(exp, tc);
}

// ensures: 1. correct number of children, 2. all children are the same type, 3.
// all children are of the correct type
template <Comparison compareType, unsigned int numChildren, typename returnType, typename T, typename... types>
static inline Expr checkChildren(Expr exp, TypeChecker &tc) {

  if (checkNumChildren <compareType, numChildren>(exp) && correctType<T, types...>(exp->first(), tc) &&
      sameType(exp, tc))
    return mk<returnType>(exp->efac());
  else
    return sort::errorTy(exp->efac());
}
struct Any {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::anyTy(exp->efac());
  }
};
} // namespace typeCheck
} // namespace op
} // namespace expr
