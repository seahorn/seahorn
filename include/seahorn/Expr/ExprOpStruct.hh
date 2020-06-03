/// structures
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

#include "llvm/ADT/SmallVector.h"

namespace expr {
namespace op {
enum class StructOpKind { MK_STRUCT, EXTRACT_VALUE, INSERT_VALUE };

namespace typeCheck {
namespace structType {
struct Struct {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    ExprVector args;
    bool wellFormed = true;

    for (auto b = exp->args_begin(), e = exp->args_end(); wellFormed && b != e;
         b++) {
      args.push_back(tc.typeOf(*b));
      wellFormed = correctType<ANY_TY>(*b, tc);
    }

    return wellFormed ? sort::structTy(args) : sort::errorTy(exp->efac());
  }
};

struct Insert {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!(checkNumChildren<Equal, 3> && isOp<MPZ>(exp->arg(1))))
      return sort::errorTy(exp->efac());

    Expr st = exp->arg(0);
    mpz_class idxZ = (getTerm<expr::mpz_class>(exp->arg(1)));
    unsigned idx = idxZ.get_ui();
    Expr v = exp->arg(2);

    if (!(idx < st->arity()))
      return sort::errorTy(exp->efac());

    ExprVector kids(st->args_begin(), st->args_end());
    kids[idx] = v;

    Expr copy = st->efac().mkNary(st->op(), kids.begin(), kids.end());

    return tc.typeOf(copy);
  }
};

struct Extract {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (!(checkNumChildren<Equal, 2> && isOp<MPZ>(exp->arg(1))))
      return sort::errorTy(exp->efac());

    Expr st = exp->arg(0);
    mpz_class idxZ = (getTerm<expr::mpz_class>(exp->arg(1)));
    unsigned idx = idxZ.get_ui();

    if (!(idx < st->arity()))
      return sort::errorTy(exp->efac());

    return tc.typeOf(st->arg(idx));
  }
};
} // namespace structType
} // namespace typeCheck

NOP_BASE(StructOp)

NOP_TYPECHECK(MK_STRUCT, "struct", FUNCTIONAL, StructOp,
              typeCheck::structType::Struct)
NOP_TYPECHECK(EXTRACT_VALUE, "extract-value", FUNCTIONAL, StructOp,
              typeCheck::structType::Extract)
NOP_TYPECHECK(INSERT_VALUE, "insert-value", FUNCTIONAL, StructOp,
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
    vals.push_back(boolop::lite(c, lhs->arg(i), rhs->arg(i)));
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
