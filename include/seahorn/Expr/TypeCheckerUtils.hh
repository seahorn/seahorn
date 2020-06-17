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
static inline bool correctTypeAny(Expr exp, TypeCheckerHelper &helper) {
  return isOp<T>(helper.typeOf(exp));
}

template <>
static inline bool correctTypeAny<ANY_TY>(Expr exp, TypeCheckerHelper &helper) {
  return !isOp<ERROR_TY>(helper.typeOf(exp));
}

// returns true if the type of the expression matches any of the passed types
// Note: checks the expression directly, not its children
// Note: ANY_TY is used as a generic type, not specifically the ANY_TY type
template <typename T, typename T2, typename... Types>
static inline bool correctTypeAny(Expr exp, TypeCheckerHelper &helper) {
  if (correctTypeAny<T>(exp, helper))
    return true;

  return correctTypeAny<T2, Types...>(exp, helper);
}

// returns true if the all children are of the passed type
template <typename T>
static inline bool correctTypeAll(Expr exp, TypeCheckerHelper &helper) {
  auto correctType = [&helper](Expr exp) { return correctTypeAny<T>(exp, helper); };
  return std::all_of(exp->args_begin(), exp->args_end(), correctType);
}

template <typename T>
static inline bool correctTypeOrder(Expr exp, TypeCheckerHelper &helper, unsigned idx) {
  return correctTypeAny<T>(exp->arg(idx), helper);
}

// returns true if child1 is of type T, child2 is of type T2 etc.
template <typename T, typename T2, typename... Types>
static inline bool correctTypeOrder(Expr exp, TypeCheckerHelper &helper, unsigned idx) {
  return correctTypeAny<T>(exp->arg(idx), helper) &&
         correctTypeOrder<T2, Types...>(exp, helper, idx + 1);
}

static inline bool sameType(std::vector<ENode *>::const_iterator begin,
                            std::vector<ENode *>::const_iterator end,
                            TypeCheckerHelper &helper) {
  Expr type = helper.typeOf(*begin);

  auto isSameType = [&helper, &type](Expr exp) {
    return type != nullptr && helper.typeOf(exp) == type;
  };
  return std::all_of(begin, end, isSameType);
}

// returns true if all children share the same type
static inline bool sameType(Expr exp, TypeCheckerHelper &helper) {
  return sameType(exp->args_begin(), exp->args_end(), helper);
}

// ensures: 1. correct number of children,
// 2. all children are of type T
template <Comparison compareType, typename T>
static inline Expr
checkChildrenAll(Expr exp, TypeCheckerHelper &helper, unsigned numChildren,
                 std::function<Expr(Expr, TypeCheckerHelper &)> returnType) {
  if (checkNumChildren<compareType>(exp, numChildren) &&
      correctTypeAll<T>(exp, helper))
    return returnType(exp, helper);

  return sort::errorTy(exp->efac());
}

// ensures: 1. correct number of children,
// 2. child1 is of type T, child 2 is the second type etc.
template <Comparison compareType, typename T, typename... Types>
static inline Expr
checkChildrenSpecific(Expr exp, TypeCheckerHelper &helper, unsigned numChildren,
                      std::function<Expr(Expr, TypeCheckerHelper &)> returnType) {
  if (checkNumChildren<compareType>(exp, numChildren) &&
      correctTypeOrder<T, Types...>(exp, helper, 0))
    return returnType(exp, helper);

  return sort::errorTy(exp->efac());
}

// ensures: 1. correct number of children,
// 2. the children are of any of the passed types,
// 3. all children are the same type
template <Comparison CompareType, typename T, typename... Types>
static inline Expr
checkChildren(Expr exp, TypeCheckerHelper &helper, unsigned numChildren,
              std::function<Expr(Expr, TypeCheckerHelper &)> returnType) {

  if (checkNumChildren<CompareType>(exp, numChildren) &&
      correctTypeAny<T, Types...>(exp->first(), helper) && sameType(exp, helper))
    return returnType(exp, helper);

  return sort::errorTy(exp->efac());
}

template <typename T>
static inline Expr returnTypeFn(Expr exp, TypeCheckerHelper &helper) {
  return mk<T>(exp->efac());
}

template <typename T, typename... Types>
static inline Expr
oneOrMore(Expr exp, TypeCheckerHelper &helper,
          std::function<Expr(Expr, TypeCheckerHelper &)> returnTypeFn) {
  return checkChildren<GreaterEqual, T, Types...>(exp, helper, 1, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr oneOrMore(Expr exp, TypeCheckerHelper &helper) {
  return checkChildren<GreaterEqual, T, Types...>(exp, helper, 1,
                                                  returnTypeFn<returnType>);
}

template <typename T, typename... Types>
static inline Expr
unary(Expr exp, TypeCheckerHelper &helper,
      std::function<Expr(Expr, TypeCheckerHelper &)> returnTypeFn) {
  return checkChildren<Equal, T, Types...>(exp, helper, 1, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr unary(Expr exp, TypeCheckerHelper &helper) {
  return checkChildren<Equal, T, Types...>(exp, helper, 1,
                                           returnTypeFn<returnType>);
}

template <typename T, typename... Types>
static inline Expr
binary(Expr exp, TypeCheckerHelper &helper,
       std::function<Expr(Expr, TypeCheckerHelper &)> returnTypeFn) {
  return checkChildren<Equal, T, Types...>(exp, helper, 2, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr binary(Expr exp, TypeCheckerHelper &helper) {
  return checkChildren<Equal, T, Types...>(exp, helper, 2,
                                           returnTypeFn<returnType>);
}

template <typename T, typename... Types>
static inline Expr nary(Expr exp, TypeCheckerHelper &helper,
                        std::function<Expr(Expr, TypeCheckerHelper &)> returnTypeFn) {
  return checkChildren<GreaterEqual, T, Types...>(exp, helper, 2, returnTypeFn);
}

template <typename returnType, typename T, typename... Types>
static inline Expr nary(Expr exp, TypeCheckerHelper &helper) {
  return checkChildren<GreaterEqual, T, Types...>(exp, helper, 2,
                                                  returnTypeFn<returnType>);
}

struct Any {
  static inline Expr inferType(Expr exp, TypeCheckerHelper &helper) {
    return sort::anyTy(exp->efac());
  }
};
} // namespace typeCheck
} // namespace op
} // namespace expr

#define NUM_TYPES INT_TY, REAL_TY, UNINT_TY, UINT_TERMINAL_TY, MPQ_TERMINAL_TY, MPZ_TERMINAL_TY