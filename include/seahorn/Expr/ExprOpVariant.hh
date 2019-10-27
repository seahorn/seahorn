/// variant expressions
#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

#include <iostream>

namespace expr {
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
}
