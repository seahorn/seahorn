/// Finite Maps
#pragma once

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
  FINITE_MAP_VAL_DEFAULT,
  CONST_FINITE_MAP,
  SET,
  GET
};
/// FiniteMap operators
NOP_BASE(FiniteMapOp)

NOP(CONST_FINITE_MAP_KEYS, "defk", FUNCTIONAL, FiniteMapOp)
NOP(CONST_FINITE_MAP_VALUES, "defv", FUNCTIONAL, FiniteMapOp)
NOP(CONST_FINITE_MAP, "defmap", FUNCTIONAL, FiniteMapOp)
NOP(FINITE_MAP_VAL_DEFAULT, "fmap-default", FUNCTIONAL, FiniteMapOp)
NOP(GET, "get", FUNCTIONAL, FiniteMapOp)
NOP(SET, "set", FUNCTIONAL, FiniteMapOp)

} // namespace op

namespace op {
namespace finite_map {

// --------------- finite map primitives ---------------------
inline Expr constFiniteMapValues(const ExprVector &values) {
  return mknary<CONST_FINITE_MAP_VALUES>(values.begin(), values.end());
}

inline Expr constFiniteMapKeys(const ExprVector &keys) {
  assert(keys.size() > 0);
  return mknary<CONST_FINITE_MAP_KEYS>(keys.begin(), keys.end());
}

// \brief builds an empty map term. `e` is the default for the unitialized
// values
inline Expr constFiniteMap(const ExprVector &keys, Expr e) {
  return mk<CONST_FINITE_MAP>(constFiniteMapKeys(keys),
                              mk<FINITE_MAP_VAL_DEFAULT>(e));
}

// construct when ALL the values of the map are known (they can be
// variables)
inline Expr constFiniteMap(const ExprVector &keys, const ExprVector &values) {
  assert(keys.size() == values.size());
  return mk<CONST_FINITE_MAP>(constFiniteMapKeys(keys),
                              constFiniteMapValues(values));
}

inline Expr get(Expr map, Expr idx) { return mk<GET>(map, idx); }
inline Expr set(Expr map, Expr idx, Expr v) { return mk<SET>(map, idx, v); }

// --------------- finite map sort ------------------------------------------
inline Expr valTy(Expr fmTy) { return fmTy->left(); }
inline Expr keys(Expr fmTy) { return fmTy->right(); }

// --------------- transformation to lambda functions ------------------------
// \brief the empty map is just the default value `edef`
inline Expr mkEmptyMap(Expr edef) { return edef; }

// creates a set of keys as a lambda function
inline Expr mkKeys(const ExprVector &keys, ExprFactory &efac) {

  Expr lmdTmp = mkTerm<mpz_class>(0, efac);
  // default value for th lambda keys: a key not defined in the fmap

  Expr keyToPos = bind::intConst(mkTerm<std::string>("x", efac));
  // this variable is used to represent where in the map values lambda term the
  // value of a key is stored. It is not affected by the sort of the keys or the
  // values. The lambda term for the keys will be expanded to (ite k1=k1 1 0)
  // and then used in an lambda term for a map: (ite ((ite k1=k1 1 0)=1) v1
  // default)), where we are using ints also.
  unsigned count = 1;
  // this loop creates a lambda term for the keys. The lambda term is of the
  // form: l1 x.(ite x == k1 1 0)
  //       ln x.(ite x == kn n (ln-1 x))
  //
  // the lambda function returns the position of the value corresponding to a
  // key in the lambda term that represents the values
  for (auto key : keys) {
    Expr nA = mkTerm<mpz_class>(count, efac);
    Expr cmp = mk<EQ>(key, keyToPos);
    Expr ite = boolop::lite(cmp, nA, op::bind::betaReduce(lmdTmp, keyToPos));
    lmdTmp = bind::abs<LAMBDA>(std::array<Expr, 1>{keyToPos}, ite);
    count++;
  }

  return lmdTmp;
}

// creates a map for keys and values, assuming that they are sorted
inline Expr mkInitializedMap(const ExprVector &keys, Expr vTy,
                             const ExprVector &values, const Expr lmdKeys,
                             ExprFactory &efac) {

  // assuming that there is a value for every key. If this is not available,
  // "initialize" it with the default value for uninitialized memory
  assert(keys.size() == values.size());

  Expr lmdMap;
  // if the vcgen is done correctly '0' should never be reached, put as default
  // value values[0]?
  if (isOpX<INT_TY>(vTy))
    lmdMap = mkTerm<mpz_class>(0, efac);
  else
    lmdMap = bv::bvnum(mkTerm<mpz_class>(0, efac), vTy);

  Expr y = bind::mkConst(mkTerm<std::string>("y", efac), vTy);
  // internal variable for the values lambda term, it must be of the value kind

  // assuming that mkKeys assigns the position in the map starting at 1
  unsigned count = 1;

  // we create lmd expressions for the map values of the form:
  //
  // l1 x.(ite (x == 1) v1 non-det)
  // ln x.(ite (x == n) vn (ln-1 x))
  for (auto v : values) {
    Expr keyToPos = mkTerm<mpz_class>(count, efac);
    Expr cmp = mk<EQ>(y, keyToPos);
    Expr ite = boolop::lite(cmp, v, op::bind::betaReduce(lmdMap, y));
    lmdMap = bind::abs<LAMBDA>(std::array<Expr, 1>{y}, ite);
    count++;
  }

  return lmdMap;
}

/// \brief Constructs get expression. Non-simplifying. None of the parameters
/// should contain map terms, they should be expanded to lambdas
//      `lmdMap` contains the values of the map as a lambda term
//      `lmdKeys` represents the keys of the map as a lambda term
//      `key` is an expression of type int or bv
inline Expr mkGetVal(Expr lmdMap, Expr lmdKeys, Expr key) {

  // assert(isOpX<LAMBDA>(lmdMap));
  // lmdMap may be a lambda or the default value: a number or a const.
  assert(isOpX<LAMBDA>(lmdKeys));

  return op::bind::betaReduce(lmdMap, op::bind::betaReduce(lmdKeys, key));
}

/// \brief Constructs set expression. Non-simplifying. None of the parameters
/// should contain map terms, they should be expanded to lambdas
//      `lmdMap` contains the values of the map as a lambda term
//      `lmdKeys` represents the keys of the map as a lambda term
inline Expr mkSetVal(Expr lmdMap, Expr lmdKeys, Expr key, Expr value,
                     ExprFactory &efac) {

  // assert(isOpX<LAMBDA>(lmdMap));
  // lmdMap may be a lambda or the default value: a number or a const.
  assert(isOpX<LAMBDA>(lmdKeys));

  Expr kTy = bind::rangeTy(bind::fname(key)); // TODO: efficiency?
  Expr x = bind::mkConst(mkTerm<std::string>("x", efac), kTy);
  // this internal variable needs to be of the same sort as keys

  Expr keyToPos = op::bind::betaReduce(lmdKeys, key);
  // keyToPos is the position in which the value for key: lmdKeys(key)
  Expr cmp = mk<EQ>(x, keyToPos);
  Expr ite = boolop::lite(cmp, value, op::bind::betaReduce(lmdMap, x));

  // lx.(ite ((lmdKeys key) == x) value (lmdMap x))
  return bind::abs<LAMBDA>(std::array<Expr, 1>{x}, ite);
}

// \brief expands the map types of fdecls into separate scalar variables
inline Expr mkMapsDecl(Expr fdecl, ExprFactory &efac) {

  assert(isOpX<FDECL>(fdecl));

  bool fmap_arg = false; // there are fmap args
  ExprVector newTypes;

  Expr fname = bind::fname(fdecl);

  for (auto type : llvm::make_range(++fdecl->args_begin(), fdecl->args_end())) {
    if (isOpX<FINITE_MAP_TY>(type)) { // the type is a FiniteMap
      fmap_arg = true;
      Expr vTy = finite_map::valTy(type);
      Expr ksTy = finite_map::keys(type);
      assert(ksTy->arity() > 0); // the map has at least one key
      auto ksIt = ksTy->args_begin();
      Expr kTy = bind::rangeTy(bind::fname(*ksIt)); // type of the key
      for (; ksIt != ksTy->args_end(); ksIt++) {
        newTypes.push_back(kTy); // new argument for key
        newTypes.push_back(vTy); // new argument for value
      }
    } else
      newTypes.push_back(type);
  }

  Expr newfname = bind::fapp(fdecl); // to go back easier, the new name includes
                                     // the old declaration
  return fmap_arg ? bind::fdecl(newfname, newTypes) : fdecl;
}

} // namespace finite_map
} // namespace op
} // namespace expr
