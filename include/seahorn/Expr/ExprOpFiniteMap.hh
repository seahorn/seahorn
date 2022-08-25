/// Finite Maps
#pragma once

#include "seahorn/Expr/TypeCheckerUtils.hh"
#include "seahorn/FiniteMapTransf.hh"

namespace expr {

namespace op {
enum class FiniteMapOpKind {
  CONST_FINITE_MAP_KEYS,
  CONST_FINITE_MAP_VALUES,
  FINITE_MAP_VAL_DEFAULT,
  CONST_FINITE_MAP,
  SET,
  GET,
  SAME_KEYS,
  CELL
};

namespace typeCheck {
namespace finiteMapType {
struct ValuesKeys;
struct ValuesDefault;
struct FiniteMap;
struct Get;
struct Set;
} // namespace finiteMapType
} // namespace typeCheck

/// FiniteMap operators
NOP_BASE(FiniteMapOp)

NOP(CONST_FINITE_MAP_KEYS, "defk", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::ValuesKeys)
NOP(CONST_FINITE_MAP_VALUES, "defv", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::ValuesKeys)
NOP(CONST_FINITE_MAP, "defmap", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::FiniteMap)
NOP(FINITE_MAP_VAL_DEFAULT, "fmap-default", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::ValuesDefault)
NOP(GET, "get", FUNCTIONAL, FiniteMapOp, typeCheck::finiteMapType::Get)
NOP(SET, "set", FUNCTIONAL, FiniteMapOp, typeCheck::finiteMapType::Set)
NOP(SAME_KEYS, "same-keys", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::FiniteMap) // TODO: type checking
NOP(CELL, "cell", FUNCTIONAL, FiniteMapOp,
    typeCheck::finiteMapType::FiniteMap) // no type checking needed, only for
                                         // expressions

namespace typeCheck {
namespace finiteMapType {

struct ValuesKeys : public TypeCheckBase {
  /// ensures that all children are the same type
  /// \return the type of its children
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnFn = [](Expr exp, TypeChecker &tc) {
      return tc.typeOf(exp->first());
    };

    return typeCheck::oneOrMore<ANY_TY>(
        exp, tc, returnFn); // children can by of any type
  }
};
struct ValuesDefault : public TypeCheckBase {
  /// ensures that there is 1 child
  /// \return the type of its child
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnFn = [](Expr exp, TypeChecker &tc) {
      return tc.typeOf(exp->first());
    };

    return typeCheck::unary<ANY_TY>(exp, tc,
                                    returnFn); // children can by of any type
  }
};

struct FiniteMap : public TypeCheckBase {
  /// ensures that the left child is a valid key type, and right is a valid
  /// value
  /// \return: FINITE_MAP_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (exp->arity() != 2 && exp->arity() != 3)
      return sort::errorTy(exp->efac());

    Expr keys = exp->left();
    Expr defval = exp->right();

    if (!isOp<CONST_FINITE_MAP_KEYS>(keys))
      return sort::errorTy(exp->efac());

    if (!isOp<FINITE_MAP_VAL_DEFAULT>(defval))
      return sort::errorTy(exp->efac());

    if (exp->arity() == 3) {
      Expr vals = exp->last();
      // TODO: check that all values are of the type of the default
      if (isOp<CONST_FINITE_MAP_VALUES>(vals)) {
        if (keys->arity() != vals->arity())
          return sort::errorTy(exp->efac());
        else if (tc.typeOf(defval) != tc.typeOf(vals->first()))
          return sort::errorTy(exp->efac());
      }
    }

    ExprVector keyVector(keys->args_begin(), keys->args_end());
    return sort::finiteMapTy(tc.typeOf(defval), keyVector);
  }
};

static inline bool checkMap(Expr exp, TypeChecker &tc, unsigned numChildren) {
  return exp->arity() == numChildren &&
         correctTypeAny<FINITE_MAP_TY>(exp->first(), tc);
}

static inline void getFiniteMapTypes(Expr exp, TypeChecker &tc, Expr &mapTy,
                                     Expr &indexTy, Expr &valTy) {
  mapTy = tc.typeOf(exp->left());
  indexTy =
      tc.typeOf(sort::finiteMapKeyTy(mapTy)
                    ->first()); // type of: FINITE_MAP_KEYS_TY -> first key
  valTy = sort::finiteMapValTy(mapTy);
}

struct Get : public TypeCheckBase {
  /// ensures that the expression's index type matches the map's index type
  /// checks for the following children (in order): map, index
  /// \return the map's value type
  /// \note this is the same as array select
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::mapType::select<FINITE_MAP_TY>(exp, tc,
                                                     getFiniteMapTypes);
  }
};

struct Set : public TypeCheckBase {
  /// ensures that the index type and value type match the map's index and value
  /// types checks for the following children (in order): map, index, value
  /// \return FINITE_MAP_TY
  /// \note this is the same as array store
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::mapType::store<FINITE_MAP_TY>(exp, tc, getFiniteMapTypes);
  }
};

} // namespace finiteMapType
} // namespace typeCheck

} // namespace op

namespace op {
namespace fmap {

// --------------- finite map primitives ---------------------
template <typename Range>
inline Expr constFiniteMapValues(const Range &values) {
  return mknary<CONST_FINITE_MAP_VALUES>(values.begin(), values.end());
}

inline Expr constFiniteMapDefault(Expr def) {
  return mk<FINITE_MAP_VAL_DEFAULT>(def);
}

template <typename Range> inline Expr constFiniteMapKeys(const Range &keys) {
  return mknary<CONST_FINITE_MAP_KEYS>(keys.begin(), keys.end());
}

// construct when ALL the values of the map are known (they can be
// variables)
// -- the iterators may be of different type
template <typename Range1, typename Range2>
inline Expr constFiniteMap(const Range1 &keys, Expr def, const Range2 &values) {
  return mk<CONST_FINITE_MAP>(constFiniteMapKeys(keys),
                              constFiniteMapDefault(def),
                              constFiniteMapValues(values));
}

inline Expr constFiniteMap(Expr keys, Expr def, Expr values) {
  return mk<CONST_FINITE_MAP>(keys, def, values);
}

inline Expr fmapValKeys(Expr fmap) { return fmap->left(); }
inline Expr fmapValDefault(Expr fmap) {
  assert(isOpX<FINITE_MAP_VAL_DEFAULT>(fmap->right()));
  return fmap->right();
}
inline Expr fmapValValues(Expr fmap) {
  assert(isOpX<CONST_FINITE_MAP_VALUES>(fmap->last()));
  return fmap->last();
}

inline bool isFmapVal(Expr m) {
  if (isOpX<CONST_FINITE_MAP>(m))
    return isOpX<CONST_FINITE_MAP_VALUES>(m->last());

  return false;
}

/// \brief Constructs get-value expression. Non-simplifying
inline Expr mkGet(Expr map, Expr idx) { return mk<GET>(map, idx); }

/// \brief Constructs get-value expression. Simplifying
inline Expr get(Expr map, Expr idx) {
  Expr get = seahorn::fmap_transf::mkGetCore(map, idx);

  if (get)
    return get;
  else
    return mkGet(map, idx);
}

/// \brief Constructs set-value expression. Non-simplifying
inline Expr mkSet(Expr map, Expr idx, Expr v) { return mk<SET>(map, idx, v); }

/// \brief Constructs get-value expression. Simplifying
inline Expr set(Expr map, Expr idx, Expr v) {
  Expr set = seahorn::fmap_transf::mkSetCore(map, idx, v);
  if (set)
    return set;
  else
    return mkSet(map, idx, v);
}

template <typename Range>
inline Expr mkConstrainKeys(Expr map, const Range &keys) {
  return mk<SAME_KEYS>(map, constFiniteMapKeys(keys));
}

inline bool isFiniteMap(const Expr e) {
  if (isOpX<ITE>(e))
    return isFiniteMap(e->right());
  else
    return bind::isFiniteMapConst(e) || isOpX<SET>(e) ||
           isOpX<CONST_FINITE_MAP>(e);
}

// --------------- transformation to lambda functions ------------------------

// \brief creates a map for keys and values, assuming that they are sorted
template <typename Range>
inline Expr mkFMapVal(const Range &keys, Expr kTy, const Range &values,
                      Expr defaultV) {

  ExprFactory &efac = kTy->efac();
  Expr y = bind::mkConst(mkTerm<std::string>("y", efac), kTy);
  // internal variable for the values lambda term, it must be of the value kind

  // we create lmd expressions for the map of size n of the form:
  //
  // l n.(vn)
  // l i.(ite (x == i) vi (ln+1 i))
  auto v_it = --values.end();
  auto k_it = --keys.end();

  Expr lmdMap = *v_it;
  for (; k_it != keys.begin(); k_it--, v_it--) {
    lmdMap = seahorn::fmap_transf::mkFMIte(mk<EQ>(y, *k_it), *v_it, lmdMap);
  }

  // first element -> TODO: change prev loop condition
  lmdMap = seahorn::fmap_transf::mkFMIte(mk<EQ>(y, *k_it), *v_it, lmdMap);

  return bind::abs<LAMBDA>(std::array<Expr, 1>{y}, lmdMap);
}

// \brief expands the map types of fdecls into separate scalar variables
inline Expr mkMapsDecl(Expr fdecl) {

  assert(isOpX<FDECL>(fdecl));

  bool fmap_arg = false; // there are fmap args
  ExprVector newTypes;

  Expr fname = bind::fname(fdecl);

  for (auto type : llvm::make_range(++fdecl->args_begin(), fdecl->args_end())) {
    if (isOpX<FINITE_MAP_TY>(type)) {
      fmap_arg = true;
      Expr vTy = sort::finiteMapValTy(type);
      Expr ksTy = sort::finiteMapKeyTy(type);
      assert(ksTy->arity() > 0); // the map has at least one key
      auto ksIt = ksTy->args_begin();
      Expr kTy = bind::rangeTy(bind::fname(*ksIt)); // type of the key
      if (ksTy->arity() == 1) {
        newTypes.push_back(vTy); // do not include key
      } else
        for (; ksIt != ksTy->args_end(); ksIt++) {
          newTypes.push_back(kTy); // new argument for key
          newTypes.push_back(vTy); // new argument for value
        }
    } else
      newTypes.push_back(type);
  }

  Expr newfname = bind::fapp(fdecl); // to go back easier, the new name
                                     // includes the old declaration
  return fmap_arg ? bind::fdecl(newfname, newTypes) : fdecl;
}

// ----------------------------------------------------------------------
//  Cell tags
// ----------------------------------------------------------------------

inline Expr mkCellTag(unsigned id1, unsigned id2, ExprFactory &efac) {
  return mk<CELL>(mkTerm<unsigned>(id1, efac), mkTerm<unsigned>(id2, efac));
}

inline Expr tagCell(Expr base, unsigned cellId, unsigned offset) {
  Expr cellE = mkCellTag(cellId, offset, base->efac());
  return bind::mkConst(variant::tag(base, cellE),
                       bind::rangeTy(bind::fname(base)));
}

inline Expr mkVarKey(Expr mapConst, Expr k, Expr kTy) {
  return bind::mkConst(variant::variant(0, variant::tag(mapConst, k)), kTy);
}

// -- creates a constant with the name get(map,k)
// also used in FiniteMapBodyVisitor
inline Expr mkVarGet(Expr mapConst, Expr k, unsigned idx, Expr vTy) {
  return bind::mkConst(variant::variant(idx, fmap::get(mapConst, k)), vTy);
}

inline Expr mkDefault(Expr base, Expr vTy) {
  return bind::mkConst(variant::tag(base, mkTerm<mpz_class>(0, vTy->efac())),
                       vTy);
}

// \brief creates a finite map value from a `mapConst` using its type, the names
// o the new constants for key-values of the map are variants with number `idx`
inline Expr mkVal(Expr mapConst, unsigned idx) {
  Expr fmapTy = bind::rangeTy(bind::name(mapConst));

  Expr vTy = sort::finiteMapValTy(fmapTy);
  Expr ksTy = sort::finiteMapKeyTy(fmapTy);
  Expr kTy = bind::rangeTy(bind::name(ksTy->arg(0)));

  ExprVector keys(ksTy->arity());
  ExprVector values(ksTy->arity());

  auto k_it = keys.begin();
  auto v_it = values.begin();
  for (auto kTy_it = ksTy->args_begin(); kTy_it != ksTy->args_end(); kTy_it++) {
    *k_it++ = mkVarKey(mapConst, *kTy_it, kTy);
    *v_it++ = mkVarGet(mapConst, *kTy_it, idx, vTy);
  }
  return constFiniteMap(keys, mkDefault(mapConst, vTy), values);
}

inline Expr expand(Expr fmv) { return seahorn::fmap_transf::expandToVal(fmv); }

} // namespace fmap
} // namespace op
} // namespace expr
