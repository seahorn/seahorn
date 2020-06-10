#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeChecker.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

/** Bit-Vector expressions

 * This file is included from middle of Expr.hh
 */
namespace expr {
namespace op {
namespace bv {
struct BvSort {
  unsigned m_width;
  BvSort(unsigned width) : m_width(width) {}
  BvSort(const BvSort &o) : m_width(o.m_width) {}

  bool operator<(const BvSort &b) const { return m_width < b.m_width; }
  bool operator==(const BvSort &b) const { return m_width == b.m_width; }
  bool operator!=(const BvSort &b) const { return m_width != b.m_width; }

  size_t hash() const {
    std::hash<unsigned> hasher;
    return hasher(m_width);
  }

  void Print(std::ostream &OS) const { OS << "bv(" << m_width << ")"; }
};
inline std::ostream &operator<<(std::ostream &OS, const BvSort &b) {
  b.Print(OS);
  return OS;
}
} // namespace bv
} // namespace op
template <> struct TerminalTrait<const op::bv::BvSort> {
  typedef const op::bv::BvSort value_type;

  static inline void print(std::ostream &OS, const op::bv::BvSort &b, int depth,
                           bool brkt) {
    OS << b;
  }
  static inline bool less(const op::bv::BvSort &b1, const op::bv::BvSort &b2) {
    return b1 < b2;
  }

  static inline bool equal_to(const op::bv::BvSort &b1,
                              const op::bv::BvSort &b2) {
    return b1 == b2;
  }

  static inline size_t hash(const op::bv::BvSort &b) { return b.hash(); }

  static TerminalKind getKind() { return TerminalKind::BVSORT; }
  static std::string name() { return "op::bv::BvSort"; }
  static inline Expr inferType(Expr exp, TypeChecker &tc) { return sort::typeTy(exp->efac()); }
};

namespace op {
typedef Terminal<const bv::BvSort> BVSORT;

namespace bv {
inline Expr bvsort(unsigned width, ExprFactory &efac) {
  return mkTerm<const BvSort>(BvSort(width), efac);
}

inline unsigned width(Expr bvsort) {
  return getTerm<const BvSort>(bvsort).m_width;
}

/// Bit-vector numeral of a given sort
/// num is an integer numeral, and bvsort is a bit-vector sort
inline Expr bvnum(Expr num, Expr bvsort) { return bind::bind(num, bvsort); }

/// bit-vector numeral of an arbitrary precision integer
inline Expr bvnum(mpz_class num, unsigned bwidth, ExprFactory &efac) {
  return bvnum(mkTerm(num, efac), bvsort(bwidth, efac));
}

/// true if v is a bit-vector numeral
inline bool is_bvnum(Expr v) {
  return isOpX<BIND>(v) && v->arity() == 2 && isOpX<MPZ>(v->arg(0)) &&
         isOpX<BVSORT>(v->arg(1));
}

inline bool isBvNum(Expr v, unsigned &w) {
  if (isOpX<BIND>(v) && v->arity() == 2 && isOpX<MPZ>(v->arg(0)) &&
      isOpX<BVSORT>(v->arg(1))) {
    w = width(v->arg(1));
    return true;
  }
  return false;
}

inline bool isBvNum(Expr v) {
  unsigned w;
  return isBvNum(v, w);
}

inline unsigned widthBvNum(Expr v) {
  assert(isBvNum(v));
  Expr sort = bind::rangeTy(v);
  return width(sort);
}

inline mpz_class toMpz(Expr v) {
  assert(is_bvnum(v));
  return getTerm<mpz_class>(v->arg(0));
}

inline Expr bvConst(Expr v, unsigned width) {
  Expr sort = bvsort(width, v->efac());
  return bind::mkConst(v, sort);
}

inline bool isBvConst(Expr v) { return bind::isConst<BVSORT>(v); }

inline unsigned widthBvConst(Expr v) {
  assert(isBvConst(v));
  Expr sort = bind::rangeTy(v->first());
  return width(sort);
}

} // namespace bv

enum class BvOpKind {
  BNOT,
  BREDAND,
  BREDOR,
  BAND,
  BOR,
  BXOR,
  BNAND,
  BNOR,
  BXNOR,
  BNEG,
  BADD,
  BSUB,
  BMUL,
  BUDIV,
  BSDIV,
  BUREM,
  BSREM,
  BSMOD,
  BULT,
  BSLT,
  BULE,
  BSLE,
  BUGE,
  BSGE,
  BUGT,
  BSGT,
  BCONCAT,
  BEXTRACT,
  BSEXT,
  BZEXT,
  BREPEAT,
  BSHL,
  BLSHR,
  BASHR,
  BROTATE_LEFT,
  BROTATE_RIGHT,
  BEXT_ROTATE_LEFT,
  BEXT_ROTATE_RIGHT,
  INT2BV,
  BV2INT,
  // Add overflow
  SADD_NO_OVERFLOW,
  UADD_NO_OVERFLOW,
  SADD_NO_UNDERFLOW,
  // Sub overflow
  SSUB_NO_OVERFLOW,
  SSUB_NO_UNDERFLOW,
  USUB_NO_UNDERFLOW,
  // Mul overflow
  SMUL_NO_OVERFLOW,
  SMUL_NO_UNDERFLOW,
  UMUL_NO_OVERFLOW
};

namespace typeCheck {
namespace bvType {

static inline Expr returnType(Expr exp, TypeChecker &tc) {
  return tc.typeOf(exp->first());
}

struct Unary {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::unary<BVSORT>(exp, tc, returnType);
  }
};

struct Binary {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::binary<BVSORT>(exp, tc, returnType);
  }
};

struct Nary {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::nary<BVSORT>(exp, tc, returnType);
  }
};

struct BinaryBool {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::binary<BOOL_TY, BVSORT>(exp, tc);
  }
};

//Returns bvsort with a width of the sum of all the children's widths
static inline Expr getExtendReturnType(Expr exp, TypeChecker &tc) {
  unsigned width = 0;
  for (auto b = exp->args_begin(), e = exp->args_end(); b != e; b++) {
    Expr bvsort = isOp<BVSORT>(*b) ? *b : tc.typeOf(*b);
    width += bv::width(bvsort);
  }

  return bv::bvsort(width, exp->efac());
}

struct Concat {

  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      return getExtendReturnType(exp, tc);
    };
    return typeCheck::checkChildrenAll<GreaterEqual, BVSORT>(exp, tc, 2,
                                                             returnTypeFn);
  }
};

struct Extend {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    if (exp->arity() != 2)
      return sort::errorTy(exp->efac());

    Expr bv = exp->left();
    Expr bvSort = exp->right(); // NOTE: bvSort should be the BVSORT operator,
                                // so we shouldn't do tc.typeOf() on it

    if (isOp<BVSORT>(tc.typeOf(bv)) && isOp<BVSORT>(bvSort))
      return getExtendReturnType(exp, tc);

    return sort::errorTy(exp->efac());
  }
};

struct Extract {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      Expr high = exp->arg(0);
      Expr low = exp->arg(1);
      Expr bv = exp->arg(2);

      unsigned width = bv::width(tc.typeOf(bv));
      unsigned highValue = getTerm<unsigned>(high);
      unsigned lowValue = getTerm<unsigned>(low);

      if ((highValue >= lowValue) && (highValue < width))
        return bv::bvsort(highValue - lowValue + 1, exp->efac());

      return sort::errorTy(exp->efac());
    };

    return typeCheck::checkChildrenSpecific<Equal, UINT, UINT, BVSORT>(
        exp, tc, 3, returnTypeFn);
  }
};

struct Bv2Int {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return typeCheck::unary<INT_TY, BVSORT>(exp, tc);
  }
};
struct Int2Bv {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      unsigned width = getTerm<unsigned>(exp->left());
      return bv::bvsort(width, exp->efac());
    };

    return typeCheck::checkChildrenSpecific<Equal, UINT, INT_TY>(exp, tc, 2,
                                                                 returnTypeFn);
  }
};

struct Rotate {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      return tc.typeOf(exp->right());
    };

    return typeCheck::checkChildrenSpecific<Equal, UINT, BVSORT>(exp, tc, 2,
                                                                 returnTypeFn);
  }
};

struct Repeat {
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    auto returnTypeFn = [](Expr exp, TypeChecker &tc) {
      unsigned timesRepeated = getTerm<unsigned>(exp->left());
      unsigned width = bv::width(tc.typeOf(exp->right()));

      return bv::bvsort(width * timesRepeated, exp->efac());
    };

    return typeCheck::checkChildrenSpecific<Equal, UINT, BVSORT>(exp, tc, 2,
                                                                 returnTypeFn);
  }
};

} // namespace bvType
} // namespace typeCheck

NOP_BASE(BvOp)
NOP_TYPECHECK(BNOT, "bvnot", FUNCTIONAL, BvOp, typeCheck::bvType::Unary)
NOP_TYPECHECK(BREDAND, "bvredand", FUNCTIONAL, BvOp, typeCheck::bvType::Unary)
NOP_TYPECHECK(BREDOR, "bvredor", FUNCTIONAL, BvOp, typeCheck::bvType::Unary)
NOP_TYPECHECK(BAND, "bvand", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BOR, "bvor", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BXOR, "bvxor", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BNAND, "bvnand", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BNOR, "bvnor", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BXNOR, "bvxnor", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BNEG, "bvneg", FUNCTIONAL, BvOp, typeCheck::bvType::Unary)
NOP_TYPECHECK(BADD, "bvadd", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BSUB, "bvsub", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BMUL, "bvmul", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BUDIV, "bvudiv", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BSDIV, "bvsdiv", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BUREM, "bvurem", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BSREM, "bvsrem", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BSMOD, "bvsmod", FUNCTIONAL, BvOp, typeCheck::bvType::Nary)
NOP_TYPECHECK(BULT, "bvult", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BSLT, "bvslt", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BULE, "bvule", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BSLE, "bvsle", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BUGE, "bvuge", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BSGE, "bvsge", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BUGT, "bvugt", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BSGT, "bvsgt", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BCONCAT, "concat", FUNCTIONAL, BvOp, typeCheck::bvType::Concat)
NOP_TYPECHECK(BEXTRACT, "extract", FUNCTIONAL, BvOp, typeCheck::bvType::Extract)
NOP_TYPECHECK(BSEXT, "bvsext", FUNCTIONAL, BvOp, typeCheck::bvType::Extend)
NOP_TYPECHECK(BZEXT, "bvzext", FUNCTIONAL, BvOp, typeCheck::bvType::Extend)
NOP_TYPECHECK(BREPEAT, "bvrepeat", FUNCTIONAL, BvOp, typeCheck::bvType::Repeat)
NOP_TYPECHECK(BSHL, "bvshl", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BLSHR, "bvlshr", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BASHR, "bvashr", FUNCTIONAL, BvOp, typeCheck::bvType::Binary)
NOP_TYPECHECK(BROTATE_LEFT, "bvrotleft", FUNCTIONAL, BvOp,
              typeCheck::bvType::Rotate)
NOP_TYPECHECK(BROTATE_RIGHT, "bvrotright", FUNCTIONAL, BvOp,
              typeCheck::bvType::Rotate)
NOP_TYPECHECK(BEXT_ROTATE_LEFT, "bvextrotleft", FUNCTIONAL, BvOp,
              typeCheck::bvType::Rotate)
NOP_TYPECHECK(BEXT_ROTATE_RIGHT, "bvextrotright", FUNCTIONAL, BvOp,
              typeCheck::bvType::Rotate)
NOP_TYPECHECK(INT2BV, "int2bv", FUNCTIONAL, BvOp, typeCheck::bvType::Int2Bv)
NOP_TYPECHECK(BV2INT, "bv2int", FUNCTIONAL, BvOp, typeCheck::bvType::Bv2Int)
// Add w Overflow
NOP_TYPECHECK(SADD_NO_OVERFLOW, "bvsadd_no_overflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
NOP_TYPECHECK(UADD_NO_OVERFLOW, "bvuadd_no_overflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
NOP_TYPECHECK(SADD_NO_UNDERFLOW, "bvbadd_no_underflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
// Sub w Overflow
NOP_TYPECHECK(SSUB_NO_OVERFLOW, "bvbsub_no_overflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
NOP_TYPECHECK(SSUB_NO_UNDERFLOW, "bvssub_no_underflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
NOP_TYPECHECK(USUB_NO_UNDERFLOW, "bvusub_no_underflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
// Mul w Overflow
NOP_TYPECHECK(SMUL_NO_OVERFLOW, "bvsmul_no_overflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
NOP_TYPECHECK(UMUL_NO_OVERFLOW, "bvumul_no_overflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
NOP_TYPECHECK(SMUL_NO_UNDERFLOW, "bvbmul_no_underflow", FUNCTIONAL, BvOp,
              typeCheck::bvType::BinaryBool)
namespace bv {
/* XXX Add helper methods as needed */

inline Expr bvnot(Expr v) { return mk<BNOT>(v); }

inline Expr extract(unsigned high, unsigned low, Expr v) {
  assert(high >= low);
  return mk<BEXTRACT>(mkTerm<unsigned>(high, v->efac()),
                      mkTerm<unsigned>(low, v->efac()), v);
}

/// high bit to extract
inline unsigned high(Expr v) { return getTerm<unsigned>(v->arg(0)); }
/// low bit to extract
inline unsigned low(Expr v) { return getTerm<unsigned>(v->arg(1)); }
/// bv argument to extract
inline Expr earg(Expr v) { return v->arg(2); }

inline Expr sext(Expr v, unsigned width) {
  return mk<BSEXT>(v, bvsort(width, v->efac()));
}

inline Expr zext(Expr v, unsigned width) {
  return mk<BZEXT>(v, bvsort(width, v->efac()));
}

inline Expr concat(Expr v, Expr u) { return mk<BCONCAT>(v, u); }

} // namespace bv
} // namespace op
} // namespace expr
