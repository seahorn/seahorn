// batch mem operations
#pragma once
#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/TypeCheckerMapUtils.hh"

namespace expr {
namespace op {
enum class MemOpKind { MEMSET_WORDS, MEMCPY_WORDS };

namespace typeCheck {
namespace memType {
struct MemSetWords : public TypeCheckBase {
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    if (exp->arity() != 4)
      return sort::errorTy(exp->efac());
    ExprVector args(exp->args_begin(), exp->args_end());
    return sort::memTy(args);
  }
};

struct MemCpyWords : public TypeCheckBase {
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    if (exp->arity() != 5)
      return sort::errorTy(exp->efac());
    ExprVector args(exp->args_begin(), exp->args_end());
    return sort::memTy(args);
  }
};
} // namespace memType
} // namespace typeCheck

NOP_BASE(MemOp)

NOP(MEMSET_WORDS, "memset_words", FUNCTIONAL, MemOp,
    typeCheck::memType::MemSetWords)
NOP(MEMCPY_WORDS, "memcpy_words", FUNCTIONAL, MemOp,
    typeCheck::memType::MemCpyWords)
} // namespace op
namespace op {
namespace memwords {
template <typename R> Expr mkSetWords(const R &args) {
  return mknary<MEMSET_WORDS>(args);
}
inline Expr setWords(Expr in_mem, Expr idx, Expr len, Expr val) {
  ExprVector args = {in_mem, idx, len, val};
  return mkSetWords(args);
}

template <typename R> Expr mkCpyWords(const R &args) {
  return mknary<MEMCPY_WORDS>(args);
}
inline Expr cpyWords(Expr dst_mem, Expr src_mem, Expr dst_idx, Expr src_idx,
                     Expr len) {
  ExprVector args = {dst_mem, src_mem, dst_idx, src_idx, len};
  return mkCpyWords(args);
}
} // namespace memwords
} // namespace op

} // namespace expr
