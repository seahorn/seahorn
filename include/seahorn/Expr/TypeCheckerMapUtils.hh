
#pragma once

#include "seahorn/Expr/ExprOpSort.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

namespace expr {
namespace op {
namespace typeCheck {
namespace mapType {

/// \return true if the map has correct layout
template <typename T>
static inline bool checkMap(Expr exp, TypeCheckerHelper &helper,
                            unsigned numChildren) {
  return exp->arity() == numChildren && correctTypeAny<T>(exp->first(), helper);
}

  /// ensures that the expression's index type matches the map's index type
  /// checks for the following children (in order): map, index
  /// \return the map's value type
template <typename T>
static inline Expr
select(Expr exp, TypeCheckerHelper &helper,
       std::function<void(Expr exp, TypeCheckerHelper &helper, Expr &mapTy,
                          Expr &indexTy, Expr &valTy)>
           getMapTypes) {
  if (!checkMap<T>(exp, helper, 2))
    return sort::errorTy(exp->efac());

  Expr mapTy;
  Expr indexTy;
  Expr valTy;

  getMapTypes(exp, helper, mapTy, indexTy, valTy);

  if (indexTy == helper.typeOf(exp->right()))
    return valTy;

  return sort::errorTy(exp->efac());
}

  /// ensures that the index type and value type match the map's index and value types
  /// checks for the following children (in order): map, index, value
  /// \return T (the map's type)
template <typename T>
static inline Expr
store(Expr exp, TypeCheckerHelper &helper,
      std::function<void(Expr exp, TypeCheckerHelper &helper, Expr &mapTy,
                         Expr &indexTy, Expr &valTy)>
          getMapTypes) {
  if (!checkMap<T>(exp, helper, 3))
    return sort::errorTy(exp->efac());

  Expr mapTy;
  Expr indexTy;
  Expr valTy;

  getMapTypes(exp, helper, mapTy, indexTy, valTy);

  if (indexTy == helper.typeOf(exp->arg(1)) &&
      valTy == helper.typeOf(exp->arg(2)))
    return mapTy;

  return sort::errorTy(exp->efac());
}

} // namespace mapType
} // namespace typeCheck
} // namespace op
} // namespace expr