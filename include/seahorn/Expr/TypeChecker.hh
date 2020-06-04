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
static inline bool correctTypeSpecific(Expr exp, TypeChecker &tc,
                                       unsigned idx) {
  return isOp<T>(tc.typeOf(exp->arg(idx)));
}

template <typename T, typename T2, typename... types>
static inline bool correctTypeSpecific(Expr exp, TypeChecker &tc,
                                       unsigned idx) {
  return isOp<T>(tc.typeOf(exp->arg(idx))) &&
         correctTypeSpecific<T2, types...>(exp, tc, idx + 1);
}

// ensures: 1. correct number of children, 2. child1 is of type T, child 2 is the second type etc.
template <Comparison compareType, unsigned int numChildren, typename T,
          typename... types>
static inline Expr
checkChildrenSpecific(Expr exp, TypeChecker &tc,
                      std::function<Expr(Expr, TypeChecker &)> returnType) {
  if (checkNumChildren<compareType, numChildren>(exp) && correctTypeSpecific<T, types...>(exp, tc, 0))
    return returnType (exp, tc);
  else
    return sort::errorTy(exp->efac());

}

// return true if the expression is of type T
template <typename T>
static inline bool correctType(Expr exp, TypeChecker &tc) {
  return isOp<T>(tc.typeOf(exp));
}

template <> static inline bool correctType<ANY_TY>(Expr exp, TypeChecker &tc) {
  return !isOp<ERROR_TY>(tc.typeOf(exp));
}

// returns true if the type of the expression matches any of the passed types
template <typename T, typename T2, typename... types>
static inline bool correctType(Expr exp, TypeChecker &tc) {
  if (isOp<T>(tc.typeOf(exp)))
    return true;

  return correctType<T2, types...>(exp, tc);
}

static inline bool sameType(std::vector<ENode *>::const_iterator begin,
                            std::vector<ENode *>::const_iterator end,
                            TypeChecker &tc) {
  Expr type = nullptr;
  bool first = true;

  auto isSameType = [&tc, &type, &first](Expr exp) {
    if (first) {
      type = tc.typeOf(exp);
      first = false;
      return true;
    }
    return type != nullptr && tc.typeOf(exp) == type;
  };
  return std::all_of(begin, end, isSameType);
}

// returns true if all children share the same type
static inline bool sameType(Expr exp, TypeChecker &tc) {
  return sameType(exp->args_begin(), exp->args_end(), tc);
}

// returns true if 1. the type of the expression matches any of the passed
// types,
// and 2. all children are of the same type
template <typename T, typename... types>
static inline bool checkType(Expr exp, TypeChecker &tc) {
  return correctType<T, types...>(exp->first(), tc) && sameType(exp, tc);
}

// ensures: 1. correct number of children, 2. all children are the same type, 3.
// all children are of the correct type
template <Comparison compareType, unsigned int numChildren, typename T,
          typename... types>
static inline Expr
checkChildren(Expr exp, TypeChecker &tc,
              std::function<Expr(Expr, TypeChecker &)> returnType) {

  if (checkNumChildren<compareType, numChildren>(exp) &&
      checkType<T, types...>(exp, tc))
    return returnType(exp, tc);
  else
    return sort::errorTy(exp->efac());
}

// ensures: 1. correct number of children, 2. all children are the same type, 3.
// all children are of the correct type
template <Comparison compareType, unsigned int numChildren, typename returnType,
          typename T, typename... types>
static inline Expr checkChildren(Expr exp, TypeChecker &tc) {
  auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
    return mk<returnType>(exp->efac());
  };

  return checkChildren<compareType, numChildren, T, types...>(exp, tc,
                                                              returnTypeFn);
}

template <typename T, typename... types>
static inline Expr
unary(Expr exp, TypeChecker &tc,
      std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<Equal, 1, T, types...>(exp, tc, returnTypeFn);
}

template <typename returnType, typename T, typename... types>
static inline Expr unary(Expr exp, TypeChecker &tc) {
  return checkChildren<Equal, 1, returnType, T, types...>(exp, tc);
}

template <typename T, typename... types>
static inline Expr
binary(Expr exp, TypeChecker &tc,
       std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<Equal, 2, T, types...>(exp, tc, returnTypeFn);
}

template <typename returnType, typename T, typename... types>
static inline Expr binary(Expr exp, TypeChecker &tc) {
  return checkChildren<Equal, 2, returnType, T, types...>(exp, tc);
}

template <typename T, typename... types>
static inline Expr nary(Expr exp, TypeChecker &tc,
                        std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<GreaterEqual, 2, T, types...>(exp, tc, returnTypeFn);
}

template <typename returnType, typename T, typename... types>
static inline Expr nary(Expr exp, TypeChecker &tc) {
  return checkChildren<GreaterEqual, 2, returnType, T, types...>(exp, tc);
}

struct Any {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::anyTy(exp->efac());
  }
};
} // namespace typeCheck
} // namespace op
} // namespace expr
