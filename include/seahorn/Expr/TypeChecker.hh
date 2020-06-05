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
enum Comparison { Equal, GreaterEqual };

template <Comparison compareType, unsigned int numChildren>
static inline bool checkNumChildren(Expr exp) {
  if (compareType == Equal)
    return exp->arity() == numChildren;
  else if (compareType == GreaterEqual)
    return exp->arity() >= numChildren;

  return false;
}

template <typename T>
static inline bool correctTypeAny(Expr exp, TypeChecker &tc) {
  return isOp<T>(tc.typeOf(exp));
}

template <>
static inline bool correctTypeAny<ANY_TY>(Expr exp, TypeChecker &tc) {
  return !isOp<ERROR_TY>(tc.typeOf(exp));
}

// returns true if the type of the expression matches any of the passed types
template <typename T, typename T2, typename... types>
static inline bool correctTypeAny(Expr exp, TypeChecker &tc) {
  if (correctTypeAny<T>(exp, tc))
    return true;

  return correctTypeAny<T2, types...>(exp, tc);
}

template <typename T>
static inline bool correctTypeOrder(Expr exp, TypeChecker &tc, unsigned idx) {
  return correctTypeAny<T>(exp->arg(idx), tc);
}

// returns true if child1 is of type T, child2 is of type T2 etc.
template <typename T, typename T2, typename... types>
static inline bool correctTypeOrder(Expr exp, TypeChecker &tc, unsigned idx) {
  return correctTypeAny<T>(exp->arg(idx), tc) &&
         correctTypeOrder<T2, types...>(exp, tc, idx + 1);
}

// returns true if all children share the same type
static inline bool sameType(Expr exp, TypeChecker &tc) {
  Expr type = tc.typeOf(exp->first());

  auto isSameType = [&tc, &type](Expr exp) {
    return type != nullptr && tc.typeOf(exp) == type;
  };
  return std::all_of(exp->args_begin(), exp->args_end(), isSameType);
}

// ensures: 1. correct number of children, 
//2. child1 is of type T, child 2 is the second type etc.
template <Comparison compareType, unsigned int numChildren, typename T,
          typename... types>
static inline Expr
checkChildrenSpecific(Expr exp, TypeChecker &tc,
                      std::function<Expr(Expr, TypeChecker &)> returnType) {
  if (checkNumChildren<compareType, numChildren>(exp) &&
      correctTypeOrder<T, types...>(exp, tc, 0))
    return returnType(exp, tc);
  else
    return sort::errorTy(exp->efac());
}

// ensures: 1. correct number of children, 
//2. the children are of any of the passed types, 
//3. all children are the same type
template <Comparison compareType, unsigned int numChildren, typename T,
          typename... types>
static inline Expr
checkChildren(Expr exp, TypeChecker &tc,
              std::function<Expr(Expr, TypeChecker &)> returnType) {

  if (checkNumChildren<compareType, numChildren>(exp) &&
      correctTypeAny<T, types...>(exp->first(), tc) && sameType(exp, tc))
    return returnType(exp, tc);
  else
    return sort::errorTy(exp->efac());
}


template <typename T>
static inline Expr returnTypeFn(Expr exp, TypeChecker &tc) {
  return mk<T>(exp->efac());
}

template <typename T, typename... types>
static inline Expr
unary(Expr exp, TypeChecker &tc,
      std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<Equal, 1, T, types...>(exp, tc, returnTypeFn);
}

template <typename returnType, typename T, typename... types>
static inline Expr unary(Expr exp, TypeChecker &tc) {
  return checkChildren<Equal, 1, T, types...>(exp, tc, returnTypeFn<returnType>);
}

template <typename T, typename... types>
static inline Expr
binary(Expr exp, TypeChecker &tc,
       std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<Equal, 2, T, types...>(exp, tc, returnTypeFn);
}

template <typename returnType, typename T, typename... types>
static inline Expr binary(Expr exp, TypeChecker &tc) {
  return checkChildren<Equal, 2, T, types...>(exp, tc, returnTypeFn<returnType>);
}

template <typename T, typename... types>
static inline Expr nary(Expr exp, TypeChecker &tc,
                        std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<GreaterEqual, 2, T, types...>(exp, tc, returnTypeFn);
}

template <typename returnType, typename T, typename... types>
static inline Expr nary(Expr exp, TypeChecker &tc) {
  return checkChildren<GreaterEqual, 2, T, types...>(exp, tc, returnTypeFn<returnType>);
}

struct Any {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::anyTy(exp->efac());
  }
};
} // namespace typeCheck
} // namespace op
} // namespace expr
