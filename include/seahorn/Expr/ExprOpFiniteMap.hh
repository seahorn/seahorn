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
enum class FiniteMapOpKind { CONST_FINITE_MAP, SET, GET };
/// FiniteMap operators
NOP_BASE(FiniteMapOp)

NOP(CONST_FINITE_MAP, "defk", FUNCTIONAL, FiniteMapOp)
NOP(GET, "get", FUNCTIONAL, FiniteMapOp)
NOP(SET, "set", FUNCTIONAL, FiniteMapOp)

} // namespace op

namespace op {
namespace finite_map {

inline Expr constFiniteMap(ExprVector keys) {
  return expr::mknary<CONST_FINITE_MAP>(keys.begin(), keys.end());
}

inline Expr get(Expr a, Expr keys, Expr idx) { return expr::mk<GET>(a, idx); }
// inline Expr get(Expr a, const ExprVector& keys, Expr idx) { return
// mk<GET>(a, keys, idx); }
inline Expr set(Expr a, Expr keys, Expr idx, Expr v) {
  return expr::mk<SET>(a, idx, v);
}
// inline Expr set(Expr a, const ExprVector& keys, Expr idx, Expr v) { return
// mk<GET>(a, keys, idx, v); }


// fresh map with unitialized values
Expr new_map_lambda(ExprFactory &efac) {
  return mkTerm<expr::mpz_class>(0, efac);
  // TODO: change 0 by the same as unitialized memory
}

// creates a set of keys as a lambda function
Expr make_lambda_map_keys(ExprVector keys, ExprFactory &efac) {

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
Expr make_map_batch_values(ExprVector keys, ExprVector values, ExprFactory &efac, Expr &lambda_keys) {

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

  Expr lmd_values = new_map_lambda(efac);

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

Expr get_map_lambda(Expr map, Expr keys, Expr key) {

  Expr pos_in_map = op::bind::betaReduce(keys, key);

  return op::bind::betaReduce(map, pos_in_map);
}

Expr set_map_lambda(Expr map, Expr keys, Expr key, Expr value,
                    ExprFactory & efac) {

  Expr x = bind::intConst(mkTerm<std::string>("x", efac));

  Expr pos_in_map = op::bind::betaReduce(keys, key);
  Expr cmp = mk<EQ>(x, pos_in_map);
  Expr ite = boolop::lite(cmp, value, op::bind::betaReduce(map, pos_in_map));
  Expr new_map = bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);

  return new_map;
}

Expr make_map_sequence_gets(ExprVector keys, ExprVector values,
                            ExprFactory &efac, Expr &lambda_keys) {

  assert(keys.size() == values.size());

  lambda_keys = make_lambda_map_keys(keys, efac);

  Expr lmd_values = new_map_lambda(efac);

  auto it_v = values.begin();

  for (auto k : keys) {
    lmd_values = set_map_lambda(lmd_values, lambda_keys, k, *it_v, efac);
    it_v++;
  }

  return lmd_values;
}

} // namespace finite_map
} // namespace op
}
