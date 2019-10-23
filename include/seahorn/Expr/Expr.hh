#pragma once

#include <typeinfo>

#include <algorithm>
#include <array>
#include <deque>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <seahorn/Expr/ExprGmp.hh>

#include <boost/container/flat_set.hpp>
#include <boost/functional/hash_fwd.hpp>
#include <boost/intrusive_ptr.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/pool/pool.hpp>
#include <boost/pool/poolfwd.hpp>
#include <boost/ptr_container/ptr_vector.hpp>

#include "llvm/ADT/STLExtras.h"
#include "llvm/ADT/iterator_range.h"
#include "llvm/Support/Casting.h"

#define mk_it_range llvm::make_range

#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprVisitor.hh"
namespace expr {
/* create a namespace op */
namespace op {}

/**********************************************************************/
/**********************************************************************/
/*                    PUBLIC API                                      */
/**********************************************************************/
/**********************************************************************/

/**********************************************************************/
/* Inspection */
/**********************************************************************/

// -- usage isOp<TYPE>(EXPR) . Returns true if top operator of
// -- expression is a subclass of TYPE.
template <typename O, typename T> bool isOp(T e) {
  return llvm::isa<O>(&eptr(e)->op());
}

// -- usage isOpX<TYPE>(EXPR) . Returns true if top operator of
// -- expression is of type TYPE.
template <typename O, typename T> bool isOpX(T e) { return isOp<O>(e); }

/**********************************************************************/
/* Creation */
/**********************************************************************/

/* Creates a nullary expression with operator T.
 * Usage: mk<TRUE> (efac)
 */
template <typename T> Expr mk(ExprFactory &f) { return f.mkTerm(T()); }

/* Creates a terminal expression with a given terminal value
 * Usage: mk (5, efac)
 */
template <typename T> Expr mkTerm(T v, ExprFactory &f) {
  Terminal<T> op(v);
  return f.mkTerm(op);
}

template <typename T> T getTerm(Expr e) {
  using term_type = Terminal<T>;
  assert(llvm::isa<term_type>(e->op()));
  return llvm::dyn_cast<const term_type>(&e->op())->get();
}

/* Creates a unary expression with a given operator.
 * Usage: mk<NEG> (exp)
 */
template <typename T> Expr mk(Expr e) { return e->efac().mkUnary(T(), e); }

template <typename T> Expr mk(Expr e1, Expr e2) {
  return e1->efac().mkBin(T(), e1, e2);
}

template <typename T> Expr mk(Expr e1, Expr e2, Expr e3) {
  return e1->efac().mkTern(T(), e1, e2, e3);
}

/**
 * Creates an nary expression with a given operator.
 * The arguments are given as first and last iterators.
 * Usage: mknary<PLUS> (v.begin (), v.end ())
 */
template <typename T, typename iterator>
Expr mknary(iterator bgn, iterator end) {
  if (bgn == end)
    return Expr(nullptr);
  return eptr(*bgn)->efac().mkNary(T(), bgn, end);
}

template <typename T, typename iterator>
Expr mknary(Expr base, iterator bgn, iterator end) {
  if (bgn == end)
    return base;
  if (std::distance(bgn, end) == 1)
    return eptr(*bgn);
  return mknary<T>(bgn, end);
}

/** boost::range versions of mknary */

template <typename T, typename Range> Expr mknary(const Range &r) {
  return mknary<T>(std::begin(r), std::end(r));
}

template <typename T, typename Range> Expr mknary(Expr base, const Range &r) {
  return mknary<T>(base, std::begin(r), std::end(r));
}

/**********************************************************************/
/* Constructors that accept explicit operators. Only use those if
   the ones above are not applicable.*/
/**********************************************************************/

/* Creates a nullary expression with a given operator.
 * Usage: mk (op, efac)
 */
inline Expr mk(const Operator &op, ExprFactory &f) { return f.mkTerm(op); }

inline Expr mk(const Operator &o, Expr e) { return e->efac().mkUnary(o, e); }

inline Expr mk(const Operator &o, Expr e1, Expr e2) {
  return e1->efac().mkBin(o, e1, e2);
}

inline Expr mk(const Operator &o, Expr e1, Expr e2, Expr e3) {
  return e1->efac().mkTern(o, e1, e2, e3);
}

template <typename iterator>
Expr mknary(const Operator &o, iterator bgn, iterator end) {
  return eptr(*bgn)->efac().mkNary(o, bgn, end);
}

/**********************************************************************/
/* Operators */
/**********************************************************************/

namespace op {
enum class BoolOpKind { TRUE, FALSE, AND, OR, XOR, NEG, IMPL, ITE, IFF };
// -- Boolean opearators
NOP_BASE(BoolOp)

/* operator definitions */
NOP(TRUE, "true", PREFIX, BoolOp)
NOP(FALSE, "false", PREFIX, BoolOp)
NOP(AND, "&&", INFIX, BoolOp)
NOP(OR, "||", INFIX, BoolOp)
NOP(XOR, "^", INFIX, BoolOp)
NOP(NEG, "!", PREFIX, BoolOp)
NOP(IMPL, "->", INFIX, BoolOp)
NOP(ITE, "ite", FUNCTIONAL, BoolOp)
NOP(IFF, "<->", INFIX, BoolOp)

namespace boolop {
// -- logical AND. Applies simplifications
inline Expr land(Expr e1, Expr e2) {
  if (e1 == e2)
    return e1;

  if (isOpX<TRUE>(e1))
    return e2;
  if (isOpX<TRUE>(e2))
    return e1;
  if (isOpX<FALSE>(e1) || isOpX<FALSE>(e2))
    return mk<FALSE>(e1->efac());

  return mk<AND>(e1, e2);
}

inline Expr lor(Expr e1, Expr e2) {
  if (isOpX<FALSE>(e1))
    return e2;
  if (isOpX<FALSE>(e2))
    return e1;
  if (isOpX<TRUE>(e1) || isOpX<TRUE>(e2))
    return mk<TRUE>(e1->efac());
  return mk<OR>(e1, e2);
}

inline Expr limp(Expr e1, Expr e2) {
  // TRUE -> x  IS x
  if (isOpX<TRUE>(e1))
    return e2;
  // x -> TRUE  IS TRUE
  if (isOpX<TRUE>(e2))
    return e2;
  // FALSE -> x IS TRUE
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());
  // x -> x IS TRUE
  if (e1 == e2)
    return mk<TRUE>(e1->efac());

  // x -> FALSE is missing since it adds a negation

  return mk<IMPL>(e1, e2);
}

inline Expr lite(Expr c, Expr t, Expr e) {
  if (isOpX<TRUE>(c))
    return t;
  if (isOpX<FALSE>(c))
    return e;
  if (t == e)
    return t;

  return mk<ITE>(c, t, e);
}

inline Expr lneg(Expr e1) {
  if (isOpX<TRUE>(e1))
    return mk<FALSE>(e1->efac());
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());

  if (isOpX<NEG>(e1))
    return e1->left();

  return mk<NEG>(e1);
}

template <typename R> Expr land(const R &r) {
  assert(std::begin(r) != std::end(r));

  // -- reduce unary AND to the operand
  if (boost::size(r) == 1)
    return *std::begin(r);

  // XXX add more logical simplifications
  return mknary<AND>(r);
}

unsigned circSize(Expr e);
unsigned circSize(const ExprVector &vec);

} // namespace boolop
} // namespace op

/// Gates
/// Gates are mutable and are not structurally hashed
namespace op {
enum class GateOpKind { OUT_G, AND_G, OR_G, NEG_G };

struct GateOp : public expr::Operator {
  GateOpKind m_kind;
  GateOp(GateOpKind k) : expr::Operator(expr::OpFamilyId::GateOp), m_kind(k) {}
  virtual bool isMutable() const { return true; }
  static bool classof(expr::Operator const *op) {
    return op->getFamilyId() == expr::OpFamilyId::GateOp;
  }
};

/// an output gate
NOP(OUT_G, "OUT_G", PREFIX, GateOp)
NOP(AND_G, "/\\", INFIX, GateOp);
NOP(OR_G, "\\/", INFIX, GateOp);
NOP(NEG_G, "~", PREFIX, GateOp);

namespace gate {
inline Expr land(Expr e1, Expr e2) {
  if (e1 == e2)
    return e1;

  if (isOpX<TRUE>(e1))
    return e2;
  if (isOpX<TRUE>(e2))
    return e1;
  if (isOpX<FALSE>(e1) || isOpX<FALSE>(e2))
    return mk<FALSE>(e1->efac());

  return mk<AND_G>(e1, e2);
}

inline Expr lor(Expr e1, Expr e2) {
  if (isOpX<FALSE>(e1))
    return e2;
  if (isOpX<FALSE>(e2))
    return e1;
  if (isOpX<TRUE>(e1) || isOpX<TRUE>(e2))
    return mk<TRUE>(e1->efac());
  return mk<OR_G>(e1, e2);
}

inline Expr lneg(Expr e1) {
  if (isOpX<TRUE>(e1))
    return mk<FALSE>(e1->efac());
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());

  if (isOpX<NEG_G>(e1) || isOpX<NEG>(e1))
    return e1->left();

  return mk<NEG_G>(e1);
}
} // namespace gate
} // namespace op

namespace op {
enum class NumericOpKind {
  PLUS,
  MINUS,
  MULT,
  DIV,
  IDIV,
  MOD,
  REM,
  UN_MINUS,
  ABS,
  PINFTY,
  NINFTY,
  ITV
};
// -- Numeric operators
NOP_BASE(NumericOp)

NOP(PLUS, "+", INFIX, NumericOp)
NOP(MINUS, "-", INFIX, NumericOp)
NOP(MULT, "*", INFIX, NumericOp)
NOP(DIV, "/", INFIX, NumericOp)
NOP(IDIV, "/", INFIX, NumericOp);
NOP(MOD, "mod", INFIX, NumericOp)
NOP(REM, "%", INFIX, NumericOp)
NOP(UN_MINUS, "-", PREFIX, NumericOp)
NOP(ABS, "abs", FUNCTIONAL, NumericOp)

NOP(PINFTY, "oo", PREFIX, NumericOp)
NOP(NINFTY, "-oo", PREFIX, NumericOp)

namespace numeric {
struct ITV_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "[";
    args[0]->Print(OS, depth, false);
    OS << ",";
    args[1]->Print(OS, depth, false);
    OS << "]";
  }
};
} // namespace numeric
NOP(ITV, "itv", numeric::ITV_PS, NumericOp)
} // namespace op

namespace op {
enum class ComparissonOpKind { EQ, NEQ, LEQ, GEQ, LT, GT };
// -- Comparisson operators
NOP_BASE(ComparissonOp)

NOP(EQ, "=", INFIX, ComparissonOp)
NOP(NEQ, "!=", INFIX, ComparissonOp)
NOP(LEQ, "<=", INFIX, ComparissonOp)
NOP(GEQ, ">=", INFIX, ComparissonOp)
NOP(LT, "<", INFIX, ComparissonOp)
NOP(GT, ">", INFIX, ComparissonOp)
} // namespace op

namespace op {
enum class MiscOpKind { NONDET, ASM, TUPLE };
// -- Not yet sorted operators
NOP_BASE(MiscOp)

/** A non-deterministic value */
NOP(NONDET, "nondet", FUNCTIONAL, MiscOp)
/** An assumption */
NOP(ASM, "ASM", ADDRESS, MiscOp)
/** A tupple */
NOP(TUPLE, "tuple", FUNCTIONAL, MiscOp)
} // namespace op

namespace op {
namespace variant {
struct PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    args[1]->Print(OS, depth, true);
    OS << "_";
    args[0]->Print(OS, depth, true);
  }
};

struct PS_TAG {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    args[1]->Print(OS, depth, true);
    OS << "!";
    args[0]->Print(OS, depth, true);
  }
};
} // namespace variant

enum class VariantOpKind { VARIANT, TAG };
NOP_BASE(VariantOp)
NOP(VARIANT, "variant", variant::PS, VariantOp)
NOP(TAG, "tag", variant::PS_TAG, VariantOp)

namespace variant {
/** Creates a variant of an expression. For example,
    `variant (1, e)` creates an expression `e_1`
*/
inline Expr variant(unsigned v, Expr e) {
  return mk<VARIANT>(mkTerm<unsigned>(v, e->efac()), e);
}

inline Expr next(Expr e) { return variant(1, e); }
inline Expr aux(Expr e) { return variant(2, e); }

inline Expr mainVariant(Expr e) { return e->right(); }
inline int variantNum(Expr e) { return getTerm<unsigned>(e->left()); }

inline Expr prime(Expr e) { return variant(1, e); }
inline bool isPrime(Expr e) { return variantNum(e) == 1; }

/** Creates an expression tagged by another expression (or
    string).  For example, `variant::tag (e, h)` creates an
    expression `e!h`.
*/

inline Expr tag(Expr e, Expr tag) { return mk<TAG>(tag, e); }

inline Expr tag(Expr e, const std::string &t) {
  return tag(e, mkTerm<std::string>(t, e->efac()));
}

inline Expr getTag(Expr e) { return e->left(); }

inline std::string getTagStr(Expr e) { return getTerm<std::string>(getTag(e)); }
} // namespace variant
} // namespace op

namespace op {
enum class SimpleTypeOpKind {
  INT_TY,
  CHAR_TY,
  REAL_TY,
  VOID_TY,
  BOOL_TY,
  UNINT_TY,
  ARRAY_TY,
  STRUCT_TY
};
NOP_BASE(SimpleTypeOp)

/// \brief Int type
NOP(INT_TY, "INT", PREFIX, SimpleTypeOp)
/// \brief Char type (UNUSED)
NOP(CHAR_TY, "CHAR", PREFIX, SimpleTypeOp)
/// \brief Real type
NOP(REAL_TY, "REAL", PREFIX, SimpleTypeOp)
/// \brief Void type
NOP(VOID_TY, "VOID", PREFIX, SimpleTypeOp)
/// \biref Boolean type
NOP(BOOL_TY, "BOOL", PREFIX, SimpleTypeOp)
/// \brief Uninterpreted type
NOP(UNINT_TY, "UNINT", PREFIX, SimpleTypeOp)
/// \brief Array type
NOP(ARRAY_TY, "ARRAY", PREFIX, SimpleTypeOp)
/// \biref Struct type
NOP(STRUCT_TY, "STRUCT", PREFIX, SimpleTypeOp)
} // namespace op

namespace op {
namespace sort {
inline Expr intTy(ExprFactory &efac) { return mk<INT_TY>(efac); }
inline Expr boolTy(ExprFactory &efac) { return mk<BOOL_TY>(efac); }
inline Expr realTy(ExprFactory &efac) { return mk<REAL_TY>(efac); }
inline Expr arrayTy(Expr indexTy, Expr valTy) {
  return mk<ARRAY_TY>(indexTy, valTy);
}
inline Expr arrayIndexTy(Expr a) { return a->left(); }
inline Expr arrayValTy(Expr a) { return a->right(); }

inline Expr structTy(Expr ty) { return mk<STRUCT_TY>(ty); }
inline Expr structTy(Expr ty1, Expr ty2) { return mk<STRUCT_TY>(ty1, ty2); }
template <typename Range> Expr structTy(const Range &ty) {
  return mknary<STRUCT_TY>(ty);
}

} // namespace sort
} // namespace op

namespace op {
enum class ArrayOpKind {
  SELECT,
  STORE,
  CONST_ARRAY,
  ARRAY_MAP,
  ARRAY_DEFAULT,
  AS_ARRAY
};
/// Array operators
NOP_BASE(ArrayOp)

NOP(SELECT, "select", FUNCTIONAL, ArrayOp)
NOP(STORE, "store", FUNCTIONAL, ArrayOp)
NOP(CONST_ARRAY, "const-array", FUNCTIONAL, ArrayOp)
NOP(ARRAY_MAP, "array-map", FUNCTIONAL, ArrayOp)
NOP(ARRAY_DEFAULT, "array-default", FUNCTIONAL, ArrayOp)
NOP(AS_ARRAY, "as-array", FUNCTIONAL, ArrayOp)
} // namespace op

namespace op {
namespace array {
inline Expr select(Expr a, Expr idx) { return mk<SELECT>(a, idx); }
inline Expr store(Expr a, Expr idx, Expr v) { return mk<STORE>(a, idx, v); }
inline Expr constArray(Expr domain, Expr v) {
  return mk<CONST_ARRAY>(domain, v);
}
inline Expr aDefault(Expr a) { return mk<ARRAY_DEFAULT>(a); }
} // namespace array
} // namespace op

namespace op {
enum class StructOpKind { MK_STRUCT, EXTRACT_VALUE, INSERT_VALUE };
NOP_BASE(StructOp)

NOP(MK_STRUCT, "struct", FUNCTIONAL, StructOp)
NOP(EXTRACT_VALUE, "extract-value", FUNCTIONAL, StructOp)
NOP(INSERT_VALUE, "insert-value", FUNCTIONAL, StructOp)
} // namespace op
namespace op {
namespace structop {

inline Expr mk(Expr v) { return expr::mk<MK_STRUCT>(v); }
inline Expr mk(Expr v0, Expr v1) { return expr::mk<MK_STRUCT>(v0, v1); }
inline Expr mk(Expr v0, Expr v1, Expr v2) {
  return expr::mk<MK_STRUCT>(v0, v1, v2);
}
template <typename R> Expr mk(const R &vals) { return mknary<MK_STRUCT>(vals); }
} // namespace structop

/// \brief Constructs insert-value expression. Non-simplifying
inline Expr mkInsertVal(Expr st, unsigned idx, Expr v) {
  mpz_class idxZ(idx);
  expr::mk<INSERT_VALUE>(st, mkTerm(idxZ, st->efac()), v);
}

/// \brief Constructs extract-value expression. Non-simplifying.
inline Expr mkExtractVal(Expr st, unsigned idx) {
  mpz_class idxZ(idx);
  expr::mk<EXTRACT_VALUE>(st, mkTerm(idxZ, st->efac()));
}

/// \brief insert-value at a given index. Simplifying.
inline Expr insertVal(Expr st, unsigned idx, Expr v) {
  if (!isOp<MK_STRUCT>(st))
    return mkInsertVal(st, idx, v);
  assert(idx < st->arity());
  ExprVector kids(st->args_begin(), st->args_end());
  kids[idx] = v;
  return structop::mk(kids);
}

/// \breif extract-value from a given index. Simplifying.
inline Expr extractVal(Expr st, unsigned idx) {
  if (!isOp<MK_STRUCT>(st))
    return mkExtractVal(st, idx);
  return st->arg(idx);
}

/// \brief Returns true if \p st is a struct value
inline bool isStructVal(Expr st) { return isOp<MK_STRUCT>(st); }

} // namespace op

namespace op {

namespace bind {
struct SCOPE_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "[" << name << " ";
    args[0]->Print(OS, depth + 2, false);
    OS << " in ";
    args[1]->Print(OS, depth + 2, false);
    OS << "]";
  }
};
struct FAPP_PS;
} // namespace bind
enum class BindOpKind { BIND, FDECL, FAPP };
NOP_BASE(BindOp)

NOP(BIND, ":", INFIX, BindOp)
/** Function declaration */
NOP(FDECL, "fdecl", PREFIX, BindOp)
/** Function application */
NOP(FAPP, "fapp", bind::FAPP_PS, BindOp)

namespace bind {
inline Expr bind(Expr name, Expr value) { return mk<BIND>(name, value); }
inline Expr name(Expr e) { return e->left(); }
inline Expr type(Expr e) { return e->right(); }
inline Expr value(Expr e) { return e->right(); }

inline Expr var(Expr name, Expr type) { return bind(name, type); }
inline Expr intVar(Expr name) { return var(name, mk<INT_TY>(name->efac())); }
inline Expr realVar(Expr name) { return var(name, mk<REAL_TY>(name->efac())); }
inline Expr boolVar(Expr name) { return var(name, mk<BOOL_TY>(name->efac())); }
inline Expr charVar(Expr name) { return var(name, mk<CHAR_TY>(name->efac())); }
inline Expr unintVar(Expr name) {
  return var(name, mk<UNINT_TY>(name->efac()));
}

template <typename T> bool isVar(Expr v) {
  return isOpX<BIND>(v) && isOpX<T>(bind::type(v));
}
inline bool isBoolVar(Expr v) { return isVar<BOOL_TY>(v); }
inline bool isIntVar(Expr v) { return isVar<INT_TY>(v); }
inline bool isRealVar(Expr v) { return isVar<REAL_TY>(v); }

inline Expr constDecl(Expr name, Expr type) { return mk<FDECL>(name, type); }
inline Expr boolConstDecl(Expr name) {
  return constDecl(name, mk<BOOL_TY>(name->efac()));
}
inline Expr intConstDecl(Expr name) {
  return constDecl(name, mk<INT_TY>(name->efac()));
}
inline Expr realConstDecl(Expr name) {
  return constDecl(name, mk<REAL_TY>(name->efac()));
}

template <typename Range> Expr fdecl(Expr fname, const Range &args) {
  // -- at least one value for range type
  assert(boost::size(args) > 0);
  ExprVector _args;
  _args.push_back(fname);
  _args.insert(_args.end(), std::begin(args), std::end(args));
  return mknary<FDECL>(_args);
}

inline bool isFdecl(Expr fdecl) { return isOpX<FDECL>(fdecl); }
inline Expr fname(Expr fdecl) { return fdecl->first(); }

inline Expr fapp(Expr fdecl) { return mk<FAPP>(fdecl); }

template <typename Range> Expr fapp(Expr fdecl, const Range &args) {
  ExprVector _args;
  _args.push_back(fdecl);
  _args.insert(_args.end(), std::begin(args), std::end(args));
  return mknary<FAPP>(_args);
}

inline Expr fapp(Expr fdecl, Expr a0, Expr a1 = Expr(), Expr a2 = Expr()) {
  ExprVector args;
  args.push_back(fdecl);

  if (a0)
    args.push_back(a0);
  if (a1)
    args.push_back(a1);
  if (a2)
    args.push_back(a2);
  return mknary<FAPP>(args);
}

inline bool isFapp(Expr fapp) { return isOpX<FAPP>(fapp); }

inline Expr rangeTy(Expr fdecl) { return fdecl->last(); }

inline size_t domainSz(Expr fdecl) {
  assert(fdecl->arity() >= 2);
  return fdecl->arity() - 2;
}

inline Expr domainTy(Expr fdecl, size_t n) {
  assert(n + 2 < fdecl->arity());
  return fdecl->arg(n + 1);
}

template <typename T> bool isFdecl(Expr v) {
  return isOpX<FDECL>(v) && isOpX<T>(rangeTy(v));
}

/** constant is an applied nullary function */
template <typename T> bool isConst(Expr v) {
  return isOpX<FAPP>(v) && v->arity() == 1 && isFdecl<T>(fname(v));
}

inline Expr mkConst(Expr name, Expr sort) {
  return fapp(constDecl(name, sort));
}
inline Expr boolConst(Expr name) { return fapp(boolConstDecl(name)); }
inline Expr intConst(Expr name) { return fapp(intConstDecl(name)); }
inline Expr realConst(Expr name) { return fapp(realConstDecl(name)); }

inline bool isBoolConst(Expr v) { return isConst<BOOL_TY>(v); }
inline bool isIntConst(Expr v) { return isConst<INT_TY>(v); }
inline bool isRealConst(Expr v) { return isConst<REAL_TY>(v); }
inline bool isArrayConst(Expr v) { return isConst<ARRAY_TY>(v); }

inline Expr typeOf(Expr v) {
  using namespace bind;
  if (isOpX<VARIANT>(v))
    return typeOf(variant::mainVariant(v));

  if (isOpX<FAPP>(v)) {
    assert(isOpX<FDECL>(v->left()));
    return rangeTy(v->left());
  }

  if (isOpX<TRUE>(v) || isOpX<FALSE>(v))
    return mk<BOOL_TY>(v->efac());
  if (isOpX<MPZ>(v))
    return mk<INT_TY>(v->efac());
  if (isOpX<MPQ>(v))
    return mk<REAL_TY>(v->efac());

  if (isOpX<BIND>(v))
    return bind::type(v);

  if (isBoolVar(v) || isBoolConst(v))
    return mk<BOOL_TY>(v->efac());
  if (isIntVar(v) || isIntConst(v))
    return mk<INT_TY>(v->efac());
  if (isRealVar(v) || isRealConst(v))
    return mk<REAL_TY>(v->efac());

  if (isOpX<SELECT>(v)) {
    Expr a = v->left();
    if (isOpX<FAPP>(a)) {
      Expr decl_a = a->left(); // decl_a is fdecl name (ARRAY idxTy valTy)
      Expr array_ty = decl_a->right();
      Expr val_ty = array_ty->right();
      return val_ty;
    }
  }

  // if (isOpX<STORE>(v)) {
  //   Expr a = v->left();
  //   if (isOpX<FAPP> (a)) {
  //     Expr decl_a = a->left(); // decl_a is fdecl name (ARRAY idxTy valTy)
  //     Expr array_ty = decl_a->right();
  //     return array_ty;
  //   }
  // }

  std::cerr << "WARNING: could not infer type of: " << *v << "\n";
  llvm_unreachable("Type inference failed");
  return Expr();
}
inline Expr sortOf(Expr v) { return typeOf(v); }

struct FAPP_PS {
  static inline void print(std::ostream &OS, int depth, int brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    if (args.size() > 1)
      OS << "(";

    // -- strip fdecl if there is one
    ENode *fname = args[0];
    if (isOpX<FDECL>(fname))
      fname = fname->arg(0);
    fname->Print(OS, depth + 2, false);

    for (unsigned i = 1; i < args.size(); ++i) {
      OS << " ";
      args[i]->Print(OS, depth + 2, false);
    }

    if (args.size() > 1)
      OS << ")";
  }
};

/// Creates a new fdecl with the same signature as the given
/// fdecl and a new name
inline Expr rename(Expr fdecl, Expr name) {
  assert(isOpX<FDECL>(fdecl));
  ExprVector _args;
  _args.reserve(fdecl->arity());
  _args.push_back(name);
  _args.insert(_args.end(), ++(fdecl->args_begin()), fdecl->args_end());
  return mknary<FDECL>(_args);
}

/// construct a new expression by applying fdecl to the same
/// arguments as fapp. For example, reapp of g(a,b) and f is f(a, b)
inline Expr reapp(Expr fapp, Expr fdecl) {
  assert(isOpX<FDECL>(fdecl));
  assert(isOpX<FAPP>(fapp));

  ExprVector _args;
  _args.reserve(fapp->arity());
  _args.push_back(fdecl);
  _args.insert(_args.end(), ++(fapp->args_begin()), fapp->args_end());
  return mknary<FAPP>(_args);
}
} // namespace bind

namespace bind {
/// returns true if an expression is a constant
class IsConst : public std::unary_function<Expr, bool> {
public:
  bool operator()(Expr e) {
    if (isOpX<VARIANT>(e))
      return this->operator()(variant::mainVariant(e));

    return isOpX<FAPP>(e) && e->arity() == 1 && isOpX<FDECL>(fname(e));
  }
};
} // namespace bind
} // namespace op
} // namespace expr

namespace expr {
namespace op {
namespace bind {
struct BoundVar {
  unsigned var;

  BoundVar(unsigned v) : var(v) {}
  BoundVar(const BoundVar &o) : var(o.var) {}

  bool operator<(const BoundVar &b) const { return var < b.var; }
  bool operator==(const BoundVar &b) const { return var == b.var; }
  bool operator!=(const BoundVar &b) const { return var != b.var; }

  size_t hash() const {
    std::hash<unsigned> hasher;
    return hasher(var);
  }

  void Print(std::ostream &OS) const { OS << "B" << var; }
};
inline std::ostream &operator<<(std::ostream &OS, const BoundVar &b) {
  b.Print(OS);
  return OS;
}
} // namespace bind
} // namespace op

template <> struct TerminalTrait<op::bind::BoundVar> {
  static inline void print(std::ostream &OS, const op::bind::BoundVar &b,
                           int depth, bool brkt) {
    OS << b;
  }
  static inline bool less(const op::bind::BoundVar &b1,
                          const op::bind::BoundVar &b2) {
    return b1 < b2;
  }

  static inline bool equal_to(const op::bind::BoundVar &b1,
                              const op::bind::BoundVar &b2) {
    return b1 == b2;
  }

  static inline size_t hash(const op::bind::BoundVar &b) { return b.hash(); }

  static TerminalKind getKind() { return TerminalKind::BVAR; }
  static std::string name() { return "bind::BoundVar"; }
};

namespace op {
using BVAR = Terminal<bind::BoundVar>;

namespace bind {
inline Expr bvar(unsigned idx, Expr type) {
  return var(mkTerm(BoundVar(idx), type->efac()), type);
}
inline Expr intBVar(unsigned idx, ExprFactory &efac) {
  return intVar(mkTerm(BoundVar(idx), efac));
}
inline Expr boolBVar(unsigned idx, ExprFactory &efac) {
  return boolVar(mkTerm(BoundVar(idx), efac));
}
inline Expr realBVar(unsigned idx, ExprFactory &efac) {
  return realVar(mkTerm(BoundVar(idx), efac));
}
inline Expr unintBVar(unsigned idx, ExprFactory &efac) {
  return unintVar(mkTerm(BoundVar(idx), efac));
}

inline bool isBVar(Expr e) {
  return isOpX<BIND>(e) && isOpX<BVAR>(bind::name(e));
}

inline unsigned bvarId(Expr e) {
  Expr t = e;
  if (isBVar(e))
    t = bind::name(e);
  assert(isOpX<BVAR>(t));
  return getTerm<BoundVar>(t).var;
}
} // namespace bind
} // namespace op

namespace details {
template <typename Range> Expr absConstants(const Range &r, Expr e);

template <typename Range> Expr subBndVars(const Range &r, Expr e);
} // namespace details

namespace op {

/**
    Binders with Locally Nameless representation.

    Arthur Charguéraud: The Locally Nameless
    Representation. J. Autom. Reasoning 49(3): 363-408 (2012)
 */

namespace bind {
struct BINDER {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "(" << name << " ";

    OS << "(";
    for (auto it = args.begin(), end = args.end() - 1; it != end; ++it) {
      (*it)->last()->Print(OS, depth + 2, true);
      if (it + 1 != end)
        OS << " ";
    }
    OS << ") ";

    args.back()->Print(OS, depth + 2, true);

    OS << ")";
  }
};
} // namespace bind

enum class BinderOpKind { FORALL, EXISTS, LAMBDA };
NOP_BASE(BinderOp)
/** Forall quantifier */
NOP(FORALL, "forall", bind::BINDER, BinderOp)
/** Exists */
NOP(EXISTS, "exists", bind::BINDER, BinderOp)
/** Lambda */
NOP(LAMBDA, "lambda", bind::BINDER, BinderOp)

namespace bind {
inline unsigned numBound(Expr e) {
  assert(e->arity() > 0);
  return e->arity() - 1;
}
inline Expr decl(Expr e, unsigned i) { return e->arg(i); }
inline Expr boundName(Expr e, unsigned i) { return fname(decl(e, i)); }
inline Expr boundSort(Expr e, unsigned i) { return rangeTy(decl(e, i)); }

inline Expr body(Expr e) { return *(--(e->args_end())); }

template <typename Op, typename Range> Expr abs(const Range &r, Expr e) {
  Expr abs = expr::details::absConstants(r, e);
  if (abs == e)
    return e;

  ExprVector args;
  args.reserve(std::distance(std::begin(r), std::end(r)) + 1);
  for (auto &v : r) {
    assert(bind::IsConst()(v));
    args.push_back(bind::fname(v));
  }

  args.push_back(abs);

  return mknary<Op>(args);
}

template <typename Op> Expr abs(Expr v, Expr e) {
  std::array<Expr, 1> a = {v};
  return abs<Op>(a, e);
}

template <typename Op> Expr abs(Expr v0, Expr v1, Expr e) {
  std::array<Expr, 2> a = {v0, v1};
  return abs<Op>(a, e);
}

template <typename Op> Expr abs(Expr v0, Expr v1, Expr v2, Expr e) {
  std::array<Expr, 3> a = {v0, v1, v2};
  return abs<Op>(a, e);
}

template <typename Range> Expr sub(const Range &r, Expr e) {
  return expr::details::subBndVars(r, e);
}

inline Expr sub(Expr v0, Expr e) {
  std::array<Expr, 1> a = {v0};
  return sub(a, e);
}

inline Expr sub(Expr v0, Expr v1, Expr e) {
  std::array<Expr, 2> a = {v0, v1};
  return sub(a, e);
}

inline Expr sub(Expr v0, Expr v1, Expr v2, Expr e) {
  std::array<Expr, 3> a = {v0, v1, v2};
  return sub(a, e);
}

inline Expr push_ite_lambda(Expr c, Expr lhs, Expr rhs) {
  assert(isOpX<LAMBDA>(lhs));
  assert(isOpX<LAMBDA>(rhs));
  // (ite (lambda ( x ) lhs) (lambda ( x ) rhs))
  ///                      ==
  // (lambda ( y ) (ite c ((lambda ( x ) lhs) y) ((lambda ( x ) rhs) y)))

  // pick one lambda term to extract abstracted terms
  Expr lambda = isOpX<LAMBDA>(lhs) ? lhs : rhs;

  // -- save abstracted term
  ExprVector args;
  args.reserve(lambda->arity());
  for (unsigned i = 0, sz = bind::numBound(lambda); i < sz; ++i) {
    args.push_back(bind::decl(lambda, i));
  }

  // -- create corresponding bound variables
  ExprVector vars;
  vars.reserve(lambda->arity());
  // -- reserve a place for lambda
  vars.push_back(Expr());

  for (unsigned i = 0, sz = bind::numBound(lambda); i < sz; ++i)
    vars.push_back(bind::bvar(i, bind::boundSort(lambda, i)));

  // -- turn lhs into an application
  vars[0] = lhs;
  Expr _lhs = mknary<FAPP>(vars);

  // -- turn rhs into an application
  vars[0] = rhs;
  Expr _rhs = mknary<FAPP>(vars);

  // -- add body of new lambda
  args.push_back(mk<ITE>(c, _lhs, _rhs));

  // -- create lambda
  return mknary<LAMBDA>(args);
}

/// \Brief create ite with lambda aware simplifications
inline Expr lite(Expr c, Expr lhs, Expr rhs) {
  if (isOpX<TRUE>(c))
    return lhs;
  if (isOpX<FALSE>(c))
    return rhs;
  if (lhs == rhs)
    return lhs;

  if (isOpX<LAMBDA>(lhs) && isOpX<LAMBDA>(rhs)) {
    return push_ite_lambda(c, lhs, rhs);
  }
  return mk<ITE>(c, lhs, rhs);
}

template <typename Range> Expr betaReduce(Expr lambda, const Range &r) {
  // -- nullptr
  if (!lambda)
    return lambda;
  // -- not lambda
  if (!isOpX<LAMBDA>(lambda))
    return lambda;

  // -- nullary
  if (numBound(lambda) == 0)
    return body(lambda);

  // -- number of arguments must match number of bound variables
  assert(std::distance(std::begin(r), std::end(r)) == numBound(lambda));

  // -- replace bound variables
  // XXX Need to decide on the order, this might be opposite from what clients
  // expect
  return sub(r, body(lambda));
}

inline Expr betaReduce(Expr lambda, Expr v0) {
  std::array<Expr, 1> a = {v0};
  return betaReduce(lambda, a);
}
inline Expr betaReduce(Expr lambda, Expr v0, Expr v1) {
  std::array<Expr, 2> a = {v0, v1};
  return betaReduce(lambda, a);
}
inline Expr betaReduce(Expr lambda, Expr v0, Expr v1, Expr v2) {
  std::array<Expr, 3> a = {v0, v1, v2};
  return betaReduce(lambda, a);
}
inline Expr betaReduce(Expr lambda, Expr v0, Expr v1, Expr v2, Expr v3) {
  std::array<Expr, 4> a = {v0, v1, v2, v3};
  return betaReduce(lambda, a);
}
} // namespace bind
} // namespace op

/**********************************************************************/
/* Utility Functions */
/**********************************************************************/

/** Size of an expression as a DAG */
size_t dagSize(Expr e);
size_t dagSize(const ExprVector &vec);
/** Size of an expression as a tree */
size_t treeSize(Expr e);

// -- replace all occurrences of s by t
Expr replaceAll(Expr exp, Expr s, Expr t);
/** Replace all occurrences of s by t while simplifying the result */
Expr replaceAllSimplify(Expr exp, Expr s, Expr t);
/** Returns true if e1 contains e2 as a sub-expression */
bool contains(Expr e1, Expr e2);

namespace op {
namespace boolop {

/**
 * Very simple simplifier for Boolean Operators
 */
Expr simplify(Expr exp);

/**
 * Very simple normalizer for AND/OR expressions
 */
Expr norm(Expr exp);

/** Gather binary Boolean operators into n-ary ones. Helps
    readability. Best done after NNF */
Expr gather(Expr exp);

/**
 * Converts to NNF. Assumes the only Boolean operators of exp
 * are AND/OR/NEG.
 */
Expr nnf(Expr exp);

/** Makes an expression pretty for printing */
Expr pp(Expr exp);

} // namespace boolop
} // namespace op
} // namespace expr

#include "ExprBv.inc"

namespace std {
/** standard order of expressions by their id */
template <> struct less<expr::ENode *> {
  bool operator()(const expr::ENode *x, const expr::ENode *y) const {
    if (x == nullptr)
      return y != nullptr;
    if (y == nullptr)
      return false;

    return x->getId() < y->getId();
  }
};
} // namespace std

#include <boost/bimap.hpp>
#include <boost/bimap/list_of.hpp>
#include <boost/bimap/unordered_set_of.hpp>
namespace expr {
using namespace boost;

/** LRU Cache */
template <typename T> class ExprCache {
  typedef boost::bimaps::bimap<boost::bimaps::unordered_set_of<ENode *>,
                               boost::bimaps::list_of<T>>
      cache_type;
  typedef typename cache_type::left_value_type value_type;
  typedef typename cache_type::right_iterator right_iterator;

  cache_type cache;
  size_t capacity;

public:
  typedef typename cache_type::left_const_iterator const_iterator;
  typedef typename cache_type::left_iterator iterator;

public:
  ExprCache(size_t c) : capacity(c) {}

  ~ExprCache() { clear(); }

  void clear() {
    for (iterator it = cache.left.begin(), end = cache.left.end(); it != end;
         ++it) {
      ENode *n = it->first;
      n->efac().Deref(n);
    }
    cache.clear();
  }

  const_iterator find(Expr e) {
    const_iterator it = cache.left.find(&*e);
    if (it != cache.left.end())
      cache.right.relocate(cache.right.end(), cache.project_right(it));
    return it;
  }

  const_iterator end() const { return cache.left.end(); }

  std::pair<iterator, bool> insert(Expr e, T &v) {
    if (cache.size() == capacity) {
      right_iterator it = cache.right.begin();
      // -- dereference a key that is about to be deleted
      ENode *old = it->second;
      old->efac().Deref(old);
      cache.right.erase(it);
    }
    ENode *n = &*e;
    n->Ref();
    return cache.left.insert(value_type(n, v));
  }

  size_t size() const { return cache.size(); }
};
} // namespace expr

namespace expr {
inline size_t hash_value(Expr e) {
  if (!e)
    return 0;
  std::hash<unsigned int> hasher;
  return hasher(e->getId());
}
} // namespace expr

/// implement boost::hash
namespace boost {
template <>
struct hash<expr::Expr> : public std::unary_function<expr::Expr, std::size_t> {
  std::size_t operator()(const expr::Expr &v) const {
    return expr::hash_value(v);
  }
};
} // namespace boost

/// implement std::hash
namespace std {
template <>
struct hash<expr::Expr> : public std::unary_function<expr::Expr, std::size_t> {
  std::size_t operator()(const expr::Expr &v) const {
    return expr::hash_value(v);
  }
};
} // namespace std

namespace expr {
namespace details {
template <typename Abs> struct ABSCST;

template <typename Range> struct AbsCst {
  typedef AbsCst<Range> this_type;

  const Range &m_r;
  std::unordered_map<Expr, unsigned> m_evmap;

  std::deque<ABSCST<this_type>> m_pinned;

  typedef std::map<unsigned, DagVisit<ABSCST<this_type>>> cache_type;
  cache_type m_cache;

  AbsCst(const Range &r);
  DagVisit<ABSCST<this_type>> &cachedVisitor(unsigned offset);
};

template <typename Abs>
struct ABSCST : public std::unary_function<Expr, VisitAction> {
  Abs &m_a;
  unsigned m_offset;

  inline ABSCST(Abs &a, unsigned offset);
  inline VisitAction operator()(Expr exp) const;
};

template <typename Range> AbsCst<Range>::AbsCst(const Range &r) : m_r(r) {
  unsigned cnt = std::distance(std::begin(r), std::end(r));
  for (const Expr &v : m_r)
    m_evmap[v] = --cnt;
}

template <typename Range>
DagVisit<ABSCST<AbsCst<Range>>> &AbsCst<Range>::cachedVisitor(unsigned offset) {
  typedef AbsCst<Range> this_type;

  auto it = m_cache.find(offset);
  if (it != m_cache.end())
    return it->second;

  m_pinned.push_back(ABSCST<this_type>(*this, offset));

  auto v = m_cache.insert(
      std::make_pair(offset, DagVisit<ABSCST<this_type>>(m_pinned.back())));
  return (v.first)->second;
}

template <typename Abs>
ABSCST<Abs>::ABSCST(Abs &a, unsigned offset) : m_a(a), m_offset(offset) {}

template <typename Abs> VisitAction ABSCST<Abs>::operator()(Expr exp) const {
  if (op::bind::isFdecl(exp))
    return VisitAction::skipKids();

  if (op::bind::IsConst()(exp)) {
    auto it = m_a.m_evmap.find(exp);
    if (it != m_a.m_evmap.end()) {
      Expr b = bind::bvar(m_offset + it->second, bind::sortOf(exp));
      return VisitAction::changeTo(b);
    }
    return VisitAction::skipKids();
  } else if (isOp<BinderOp>(exp)) {
    auto &dv = m_a.cachedVisitor(m_offset + 1);
    ExprVector kids(exp->args_begin(), exp->args_end());
    Expr &last = kids.back();
    last = dv(last);
    return VisitAction::changeTo(exp->efac().mkNary(exp->op(), kids));
  }

  return VisitAction::doKids();
}

template <typename Range> Expr absConstants(const Range &r, Expr e) {
  AbsCst<Range> a(r);
  auto v = ABSCST<AbsCst<Range>>(a, 0);
  return dagVisit(v, e);
}

template <typename Sub> struct SUBBND;

template <typename Range> struct SubBnd {
  typedef SubBnd<Range> this_type;

  const Range &m_r;
  unsigned m_sz;
  std::vector<SUBBND<this_type>> m_pinned;
  typedef std::map<unsigned, DagVisit<SUBBND<this_type>>> cache_type;
  cache_type m_cache;

  SubBnd(const Range &r) : m_r(r) {
    m_sz = std::distance(std::begin(m_r), std::end(m_r));
  }

  DagVisit<SUBBND<this_type>> &cachedVisitor(unsigned offset);

  Expr sub(unsigned idx) {
    if (idx >= m_sz)
      return Expr(0);
    auto it = std::end(m_r) - 1 - idx;
    return *it;
  }
};

template <typename Sub>
struct SUBBND : public std::unary_function<Expr, VisitAction> {
  Sub &m_a;
  unsigned m_offset;

  SUBBND(Sub &a, unsigned offset) : m_a(a), m_offset(offset){};

  VisitAction operator()(Expr exp) const {
    if (bind::isFdecl(exp))
      return VisitAction::skipKids();
    else if (bind::isBVar(exp)) {
      unsigned idx = bind::bvarId(exp);
      if (idx < m_offset)
        return VisitAction::skipKids();

      Expr u = m_a.sub(idx - m_offset);
      return u ? VisitAction::changeTo(u) : VisitAction::skipKids();
    } else if (isOp<BinderOp>(exp)) {
      auto &dv = m_a.cachedVisitor(m_offset + 1);
      ExprVector kids(exp->args_begin(), exp->args_end());
      Expr &last = kids.back();
      last = dv(last);
      return VisitAction::changeTo(exp->efac().mkNary(exp->op(), kids));
    }
    return VisitAction::doKids();
  }
};

template <typename Range>
DagVisit<SUBBND<SubBnd<Range>>> &SubBnd<Range>::cachedVisitor(unsigned offset) {
  typedef SubBnd<Range> this_type;
  auto it = m_cache.find(offset);
  if (it != m_cache.end())
    return it->second;

  m_pinned.push_back(SUBBND<this_type>(*this, offset));
  auto v = m_cache.insert(
      std::make_pair(offset, DagVisit<SUBBND<this_type>>(m_pinned.back())));
  return (v.first)->second;
}

template <typename Range> Expr subBndVars(const Range &r, Expr e) {
  SubBnd<Range> a(r);
  auto v = SUBBND<SubBnd<Range>>(a, 0);
  return dagVisit(v, e);
}
} // namespace details
} // namespace expr
