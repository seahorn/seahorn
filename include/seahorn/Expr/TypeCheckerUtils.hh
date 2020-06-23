#pragma once

#include "seahorn/Expr/ExprOpSort.hh"
#include "seahorn/Expr/TypeChecker.hh"

namespace expr {
namespace op {
namespace typeCheck {
enum Comparison { Equal, GreaterEqual };

template <Comparison compareType>
static inline bool checkNumChildren(Expr exp, unsigned numChildren) {
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
// Note: checks the expression directly, not its children
// Note: ANY_TY is used as a generic type, not specifically the ANY_TY type
template <typename T, typename T2, typename... Types>
static inline bool correctTypeAny(Expr exp, TypeChecker &tc) {
  if (correctTypeAny<T>(exp, tc))
    return true;

  return correctTypeAny<T2, Types...>(exp, tc);
}

// returns true if the all children are of the passed type
template <typename T>
static inline bool correctTypeAll(Expr exp, TypeChecker &tc) {
  auto correctType = [&tc](Expr exp) { return correctTypeAny<T>(exp, tc); };
  return std::all_of(exp->args_begin(), exp->args_end(), correctType);
}

template <typename T>
static inline bool correctTypeOrder(Expr exp, TypeChecker &tc, unsigned idx) {
  return correctTypeAny<T>(exp->arg(idx), tc);
}

// returns true if child1 is of type T, child2 is of type T2 etc.
template <typename T, typename T2, typename... Types>
static inline bool correctTypeOrder(Expr exp, TypeChecker &tc, unsigned idx) {
  return correctTypeAny<T>(exp->arg(idx), tc) &&
         correctTypeOrder<T2, Types...>(exp, tc, idx + 1);
}

static inline bool sameType(std::vector<ENode *>::const_iterator begin,
                            std::vector<ENode *>::const_iterator end,
                            TypeChecker &tc) {
  Expr type = tc.typeOf(*begin);

  auto isSameType = [&tc, &type](Expr exp) {
    return type != nullptr && tc.typeOf(exp) == type;
  };
  return std::all_of(begin, end, isSameType);
}

// returns true if all children share the same type
static inline bool sameType(Expr exp, TypeChecker &tc) {
  return sameType(exp->args_begin(), exp->args_end(), tc);
}

// ensures: 1. correct number of children,
// 2. all children are of type T
template <Comparison compareType, typename T>
static inline Expr
checkChildrenAll(Expr exp, TypeChecker &tc, unsigned numChildren,
                 std::function<Expr(Expr, TypeChecker &)> returnType) {
  if (checkNumChildren<compareType>(exp, numChildren) &&
      correctTypeAll<T>(exp, tc))
    return returnType(exp, tc);

  return sort::errorTy(exp->efac());
}

// ensures: 1. correct number of children,
// 2. child1 is of type T, child 2 is the second type etc.
template <Comparison compareType, typename T, typename... Types>
static inline Expr
checkChildrenSpecific(Expr exp, TypeChecker &tc, unsigned numChildren,
                      std::function<Expr(Expr, TypeChecker &)> returnType) {
  if (checkNumChildren<compareType>(exp, numChildren) &&
      correctTypeOrder<T, Types...>(exp, tc, 0))
    return returnType(exp, tc);

  return sort::errorTy(exp->efac());
}

// ensures: 1. correct number of children,
// 2. the children are of any of the passed types,
// 3. all children are the same type
template <Comparison CompareType, typename T, typename... Types>
static inline Expr
checkChildren(Expr exp, TypeChecker &tc, unsigned numChildren,
              std::function<Expr(Expr, TypeChecker &)> returnType) {

  if (checkNumChildren<CompareType>(exp, numChildren) &&
      correctTypeAny<T, Types...>(exp->first(), tc) && sameType(exp, tc))
    return returnType(exp, tc);

  return sort::errorTy(exp->efac());
}

template <typename T>
static inline Expr returnTypeFn(Expr exp, TypeChecker &tc) {
  return mk<T>(exp->efac());
}

template <typename T, typename... Types>
static inline Expr
oneOrMore(Expr exp, TypeChecker &tc,
          std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<GreaterEqual, T, Types...>(exp, tc, 1, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr oneOrMore(Expr exp, TypeChecker &tc) {
  return checkChildren<GreaterEqual, T, Types...>(exp, tc, 1,
                                                  returnTypeFn<returnType>);
}

template <typename T, typename... Types>
static inline Expr
unary(Expr exp, TypeChecker &tc,
      std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<Equal, T, Types...>(exp, tc, 1, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr unary(Expr exp, TypeChecker &tc) {
  return checkChildren<Equal, T, Types...>(exp, tc, 1,
                                           returnTypeFn<returnType>);
}

template <typename T, typename... Types>
static inline Expr
binary(Expr exp, TypeChecker &tc,
       std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<Equal, T, Types...>(exp, tc, 2, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr binary(Expr exp, TypeChecker &tc) {
  return checkChildren<Equal, T, Types...>(exp, tc, 2,
                                           returnTypeFn<returnType>);
}

template <typename T, typename... Types>
static inline Expr nary(Expr exp, TypeChecker &tc,
                        std::function<Expr(Expr, TypeChecker &)> returnTypeFn) {
  return checkChildren<GreaterEqual, T, Types...>(exp, tc, 2, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr nary(Expr exp, TypeChecker &tc) {
  return checkChildren<GreaterEqual, T, Types...>(exp, tc, 2,
                                                  returnTypeFn<returnType>);
}

struct Any {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::anyTy(exp->efac());
  }
};
} // namespace typeCheck
} // namespace op
} // namespace expr

#define NUM_TYPES INT_TY, REAL_TY, UNINT_TY