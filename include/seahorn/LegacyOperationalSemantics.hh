#pragma once

#include "seahorn/OperationalSemantics.hh"
#include "seahorn/SymStore.hh"
#include "seahorn/Expr/Expr.hh"
#include "llvm/IR/InstVisitor.h"

namespace seahorn {
using namespace llvm;
using namespace expr;

/// \brief Abstract interface for Operational Semantics
class LegacyOperationalSemantics : public OperationalSemantics {
public:
  explicit LegacyOperationalSemantics(ExprFactory &efac)
      : OperationalSemantics(efac){};
  explicit LegacyOperationalSemantics(const LegacyOperationalSemantics &o)
      : OperationalSemantics(o){};
  ~LegacyOperationalSemantics() override = default;

  /// \brief Returns a symbolic register correspond to llvm::Value
  /// Deprecated. See mkSymbReg
  virtual Expr symb(const Value &v) = 0;

  /// \brief Returns a symbolic register correspond to llvm::Value
  Expr mkSymbReg(const Value &v, OpSemContext &ctx) override { return symb(v); }
  Expr getSymbReg(const Value &v, const OpSemContext &ctx) const override {
    return const_cast<LegacyOperationalSemantics *>(this)->symb(v);
  }

  /// \brief Returns special symbolic register that contains the value
  /// at which memory region with id \p id begins
  virtual Expr memStart(unsigned id) = 0;
  /// \brief Returns special symbolic register that contains the value
  /// at which memory region with id \p id ends
  virtual Expr memEnd(unsigned id) = 0;

  void exec(const llvm::BasicBlock &bb, OpSemContext &ctx) override {
    exec(ctx.values(), bb, ctx.side(), ctx.getPathCond());
  }

  void execPhi(const llvm::BasicBlock &bb, const llvm::BasicBlock &from,
               OpSemContext &ctx) override {
    execPhi(ctx.values(), bb, from, ctx.side(), ctx.getPathCond());
  }

  void execEdg(const llvm::BasicBlock &src, const llvm::BasicBlock &dst,
               OpSemContext &ctx) override {
    execEdg(ctx.values(), src, dst, ctx.side());
  }

  void execBr(const llvm::BasicBlock &src, const llvm::BasicBlock &dst,
              OpSemContext &ctx) override {
    execBr(ctx.values(), src, dst, ctx.side(), ctx.getPathCond());
  }

  /// Deprecated old interface
  virtual void exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
                    Expr act) = 0;

  virtual void execPhi(SymStore &s, const BasicBlock &bb,
                       const BasicBlock &from, ExprVector &side, Expr act) = 0;

  virtual void execEdg(SymStore &s, const BasicBlock &src,
                       const BasicBlock &dst, ExprVector &side) = 0;

  virtual void execBr(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                      ExprVector &side, Expr act) = 0;
};

/// \brief Evaluate (read) all arguments of \p fi in store \p s
///
/// Reads all arguments corresponding to the given \c FunctionInfo \p fi in the
/// given store \p sym. The result of the evaluation is stored in \p out.
template <typename OutputIterator>
void evalArgs(const FunctionInfo &fi, LegacyOperationalSemantics &sem,
              SymStore &s, OutputIterator out) {
  for (auto *v : fi.regions)
    *out++ = s.read(sem.symb(*v));
  for (auto *a : fi.args)
    *out++ = s.read(sem.symb(*a));
  for (auto *g : fi.globals)
    *out++ = s.read(sem.symb(*g));
  if (fi.ret)
    *out++ = s.read(sem.symb(*fi.ret));
}

} // namespace seahorn
