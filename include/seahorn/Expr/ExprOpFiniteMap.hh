/// Finite Maps
#pragma once

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace op {
enum class FiniteMapOpKind {
  CONST_FINITE_MAP_KEYS,
  CONST_FINITE_MAP_VALUES,
  CONST_FINITE_MAP,
  SET,
  GET
};
/// FiniteMap operators
NOP_BASE(FiniteMapOp)

NOP(CONST_FINITE_MAP_KEYS, "defk", FUNCTIONAL, FiniteMapOp)
NOP(CONST_FINITE_MAP_VALUES, "defv", FUNCTIONAL, FiniteMapOp)
NOP(CONST_FINITE_MAP, "defmap", FUNCTIONAL, FiniteMapOp)
NOP(GET, "get", FUNCTIONAL, FiniteMapOp)
NOP(SET, "set", FUNCTIONAL, FiniteMapOp)

} // namespace op

namespace op {
namespace finite_map {

inline Expr constFiniteMapValues(ExprVector &values) {
  return expr::mknary<CONST_FINITE_MAP_VALUES>(values.begin(), values.end());
}

inline Expr constFiniteMap(ExprVector &keys) {
  return expr::mknary<CONST_FINITE_MAP_KEYS>(keys.begin(), keys.end());
}
// especial construct when ALL the values of the map are known (they can be
// variables)
inline Expr constFiniteMap(ExprVector &keys, ExprVector &values) {
  assert(keys.size() == values.size());
  return expr::mk<CONST_FINITE_MAP>(constFiniteMap(keys),
                                    constFiniteMapValues(values));
}

inline Expr get(Expr map, Expr idx) {
  return expr::mk<GET>(map, idx);
}
inline Expr set(Expr map, Expr idx, Expr v) {
  return expr::mk<SET>(map, idx, v);
}

// \brief fresh map with unitialized values
inline Expr mkEmptyMap(ExprFactory &efac) {
  return mkTerm<expr::mpz_class>(0, efac);
  // TODO: change 0 by the same as unitialized memory?
}

// creates a set of keys as a lambda function
inline Expr mkKeys(ExprVector &keys, ExprFactory &efac) {

  Expr x = bind::intConst(mkTerm<std::string>("x", efac));

  Expr lmd_bot = bind::abs<LAMBDA>(std::array<Expr, 1>{x},
                                   mkTerm<expr::mpz_class>(0, efac));
  // up to here, it will be the same for all keysets

  int count = 1;

  Expr lmd_tmp = lmd_bot;

  for (auto key : keys) {
    Expr nA = mkTerm<expr::mpz_class>(count, efac);
    Expr cmp = mk<EQ>(key, x);
    Expr ite = boolop::lite(cmp, nA, op::bind::betaReduce(lmd_tmp, x));
    lmd_tmp = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
    count++;
  }

  return lmd_tmp;
}

// creates a map for keys and values, assuming that they are sorted
// old make_map_batch_values
inline Expr mkInitializedMap(ExprVector &keys, ExprVector &values,
                             ExprFactory &efac, Expr &lambda_keys) {

  // assuming that there is a value for every key. If this is not available,
  // "initialize" it with the default value for uninitialized memory
  assert(keys.size() == values.size());

  Expr x = bind::intConst(mkTerm<std::string>("x", efac));

  Expr lmd_bot = bind::abs<LAMBDA>(std::array<Expr, 1>{x},
                                   mkTerm<expr::mpz_class>(0, efac));
  int count = 1;
  Expr lmd_tmp = lmd_bot;

  for (auto key : keys) {
    Expr nA = mkTerm<expr::mpz_class>(count, efac);
    Expr cmp = mk<EQ>(key, x);
    Expr ite = boolop::lite(cmp, nA, op::bind::betaReduce(lmd_tmp, x));
    lmd_tmp = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
    count++;
  }

  lambda_keys = lmd_tmp;

  count = 1;

  Expr lmd_values = mkEmptyMap(efac);

  for (auto v : values) {
    Expr pos_in_map = mkTerm<expr::mpz_class>(count, efac);
    Expr cmp = mk<EQ>(x, pos_in_map);
    Expr ite =
        boolop::lite(cmp, v, op::bind::betaReduce(lmd_values, x));
    lmd_values = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
    count++;
  }

  return lmd_values;
}

/// \brief Constructs get expression. Non-simplifying
inline Expr mkGetVal(Expr map, Expr keys, Expr key) {

  Expr pos_in_map = op::bind::betaReduce(keys, key);

  return op::bind::betaReduce(map, pos_in_map);
}

/// \brief Constructs set expression. Non-simplifying
inline Expr mkSetVal(Expr map, Expr keys, Expr key, Expr value,
                     ExprFactory &efac) {

  Expr x = bind::intConst(mkTerm<std::string>("x", efac));

  Expr pos_in_map = op::bind::betaReduce(keys, key);
  Expr cmp = mk<EQ>(x, pos_in_map);
  Expr ite = boolop::lite(cmp, value, op::bind::betaReduce(map, pos_in_map));
  Expr new_map = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);

  return new_map;
}

// \brief expands the map types of fdecls into separate scalar variables
inline Expr mkMapsDecl(Expr fdecl, ExprFactory &efac) {

  assert(isOpX<FDECL>(fdecl));

  ExprVector newTypes;

  Expr iTy = op::sort::intTy(efac);
  Expr fname = bind::fname(fdecl);

  for (auto tyIt = fdecl->args_begin(); tyIt != fdecl->args_end(); tyIt++) {
    Expr type = *tyIt;
    if (isOpX<FINITE_MAP_TY>(type)) {                 // the type is a FiniteMap
      assert(type->args_begin() != type->args_end()); // the map has at
                                                      // least one key
      for (auto kIt = type->args_begin(); kIt != type->args_end(); kIt++) {
        newTypes.push_back(iTy); // new argument for key
        newTypes.push_back(iTy); // new argument for value
      }
    } else
      newTypes.push_back(type);
  }

  Expr newfname = bind::fapp(fdecl); // to go back easier, the new name includes
                                     // the old declaration

  // change new name by fapp for prettier printing, can it be done with empty
  // arguments?

  return bind::fdecl(newfname, newTypes);
}

// This function is just for testing // internal
//
// \brief builds an initialized map as a sequence of gets (as opposed to
// mkInitializedMap), which builds one ite expression directly
inline Expr make_map_sequence_gets(ExprVector & keys, ExprVector & values,
                                   ExprFactory & efac, Expr & lambda_keys) {
  assert(keys.size() == values.size());

  lambda_keys = mkKeys(keys, efac);
  Expr lmd_values = mkEmptyMap(efac);

  auto it_v = values.begin();
  for (auto k : keys) {
    lmd_values = mkSetVal(lmd_values, lambda_keys, k, *it_v, efac);
    it_v++;
  }

  return lmd_values;
}

} // namespace finite_map
} // namespace op
}
