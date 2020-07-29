/// structures
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBinder.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

#include "llvm/ADT/SmallVector.h"

namespace expr {
namespace op {
enum class StructOpKind { MK_STRUCT, EXTRACT_VALUE, INSERT_VALUE };

namespace typeCheck {
namespace structType {
struct Struct  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    ExprVector childrenTypes;
    bool wellFormed = true;

    // create a vector with the types of the struct's children
    // if any of the children are error types then leave and return an error
    // type
    for (auto b = exp->args_begin(), e = exp->args_end(); wellFormed && b != e;
         b++) {
      childrenTypes.push_back(tc.typeOf(*b));
      wellFormed = correctTypeAny<ANY_TY>(*b, tc);
    }

    return wellFormed ? sort::structTy(childrenTypes)
                      : sort::errorTy(exp->efac());
  }
};

static inline Expr getStruct(Expr exp) { return exp->arg(0); }

static inline unsigned getIndex(Expr exp) {
  mpz_class idxZ = (getTerm<expr::mpz_class>(exp->arg(1)));
  return idxZ.get_ui();
}

static inline bool structCheck(Expr exp, unsigned numChildren) {
  return exp->arity() == numChildren && isOp<MPZ>(exp->arg(1)) &&
         getIndex(exp) < getStruct(exp)->arity();
}

struct Insert  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!structCheck(exp, 3))
      return sort::errorTy(exp->efac());

    Expr st = getStruct(exp);
    unsigned idx = getIndex(exp);
    Expr v = exp->arg(2);

    // Create a copy of the struct exp with the value v insert into
    // the correct spot
    ExprVector kids(st->args_begin(), st->args_end());
    kids[idx] = v;

    Expr copy = st->efac().mkNary(st->op(), kids.begin(), kids.end());

    return tc.typeOf(copy);
  }
};

struct Extract  : public TypeCheckBase{
  inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!structCheck(exp, 2))
      return sort::errorTy(exp->efac());

    Expr st = getStruct(exp);
    unsigned idx = getIndex(exp);

    return tc.typeOf(st->arg(idx));
  }
};
} // namespace structType
} // namespace typeCheck

NOP_BASE(StructOp)

NOP(MK_STRUCT, "struct", FUNCTIONAL, StructOp, typeCheck::structType::Struct)
NOP(EXTRACT_VALUE, "extract-value", FUNCTIONAL, StructOp,
    typeCheck::structType::Extract)
NOP(INSERT_VALUE, "insert-value", FUNCTIONAL, StructOp,
    typeCheck::structType::Insert)
} // namespace op
namespace op {
namespace strct {

inline Expr mk(Expr v) { return expr::mk<MK_STRUCT>(v); }
inline Expr mk(Expr v0, Expr v1) { return expr::mk<MK_STRUCT>(v0, v1); }
inline Expr mk(Expr v0, Expr v1, Expr v2) {
  return expr::mk<MK_STRUCT>(v0, v1, v2);
}
template <typename R> Expr mk(const R &vals) { return mknary<MK_STRUCT>(vals); }

/// \brief Constructs insert-value expression. Non-simplifying
inline Expr mkInsertVal(Expr st, unsigned idx, Expr v) {
  mpz_class idxZ(idx);
  return expr::mk<INSERT_VALUE>(st, mkTerm(idxZ, st->efac()), v);
}

/// \brief Constructs extract-value expression. Non-simplifying.
inline Expr mkExtractVal(Expr st, unsigned idx) {
  mpz_class idxZ(idx);
  return expr::mk<EXTRACT_VALUE>(st, mkTerm(idxZ, st->efac()));
}

/// \brief insert-value at a given index. Simplifying.
inline Expr insertVal(Expr st, unsigned idx, Expr v) {
  if (!isOp<MK_STRUCT>(st))
    return mkInsertVal(st, idx, v);
  assert(idx < st->arity());
  ExprVector kids(st->args_begin(), st->args_end());
  kids[idx] = v;
  return strct::mk(kids);
}

/// \breif extract-value from a given index. Simplifying.
inline Expr extractVal(Expr st, unsigned idx) {
  if (!isOp<MK_STRUCT>(st))
    return mkExtractVal(st, idx);
  return st->arg(idx);
}

/// \brief Returns true if \p st is a struct value
inline bool isStructVal(Expr st) { return isOp<MK_STRUCT>(st); }

inline Expr push_ite_struct(Expr c, Expr lhs, Expr rhs) {
  assert(isStructVal(lhs));
  assert(isStructVal(rhs));
  assert(lhs->arity() == rhs->arity());

  llvm::SmallVector<Expr, 8> vals;
  for (unsigned i = 0, sz = lhs->arity(); i < sz; ++i) {
    vals.push_back(bind::lite(c, lhs->arg(i), rhs->arg(i)));
  }
  return strct::mk(vals);
}

inline Expr mkEq(Expr lhs, Expr rhs) {
  if (isStructVal(lhs) && isStructVal(rhs) && lhs->arity() == rhs->arity()) {
    llvm::SmallVector<Expr, 8> kids;
    for (unsigned i = 0, sz = lhs->arity(); i < sz; ++i) {
      kids.push_back(mkEq(lhs->arg(i), rhs->arg(i)));
    }
    return mknary<AND>(mk<TRUE>(lhs->efac()), kids.begin(), kids.end());
  }
  return mk<EQ>(lhs, rhs);
}

} // namespace strct
} // namespace op

} // namespace expr
