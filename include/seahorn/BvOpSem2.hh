#pragma once

#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/OpSem.hh"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Pass.h"

#include <boost/container/flat_set.hpp>

namespace llvm {
class GetElementPtrInst;
}

namespace seahorn {

namespace bvop_details {
class Bv2OpSemContext;
class OpSemMemManager;
class OpSemBase;
class OpSemVisitor;
class OpSemPhiVisitor;
} // namespace bvop_details

/**
   Bit-precise operational semantics for LLVM (take 2)

   Fairly accurate representation of LLVM semantics without
   considering undefined behaviour. Most operators are mapped
   directly to their logical equivalent SMT-LIB representation.

   Memory is modelled by arrays.
 */
class Bv2OpSem : public OpSem {
  friend class bvop_details::OpSemBase;
  friend class bvop_details::OpSemVisitor;
  friend class bvop_details::OpSemPhiVisitor;
  friend class bvop_details::Bv2OpSemContext;

  Pass &m_pass;
  TrackLevel m_trackLvl;

  const DataLayout *m_td;
  const TargetLibraryInfo *m_tli;
  const CanFail *m_canFail;

  /// Evaluates constant expression into a value
  Optional<GenericValue> getConstantValue(const Constant *C);

public:
  Bv2OpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
           TrackLevel trackLvl = MEM);

  Bv2OpSem(const Bv2OpSem &o);

  const DataLayout &getTD() {
    assert(m_td);
    return *m_td;
  }

  OpSemContextPtr mkContext(SymStore &values, ExprVector &side) override;

  /// \brief Executes one intra-procedural instructions in the
  /// current context Assumes that current instruction is not a
  /// branch Returns true if instruction was executed and false if
  /// there is no suitable instruction found
  bool intraStep(bvop_details::Bv2OpSemContext &C);
  /// \brief Executes one intra-procedural branch instruction in the
  /// current context. Assumes that current instruction is a branch
  void intraBr(bvop_details::Bv2OpSemContext &C, const BasicBlock &dst);

  /// \brief Execute all PHINode instructions of the current basic block
  /// \brief assuming that control flows from previous basic block
  void intraPhi(bvop_details::Bv2OpSemContext &C);

  Expr errorFlag(const BasicBlock &BB) override;


  void exec(const BasicBlock &bb, OpSemContext &_ctx) override {
    exec(bb, ctx(_ctx));
  }
  void execPhi(const BasicBlock &bb, const BasicBlock &from,
               OpSemContext &_ctx) override {
    execPhi(bb, from, ctx(_ctx));
  }
  void execEdg(const BasicBlock &src, const BasicBlock &dst,
               OpSemContext &_ctx) override {
    execEdg(src, dst, ctx(_ctx));
  }
  void execBr(const BasicBlock &src, const BasicBlock &dst,
              OpSemContext &_ctx) override {
    execBr(src, dst, ctx(_ctx));
  }

  void exec(const BasicBlock &bb, bvop_details::Bv2OpSemContext &ctx);
  void execPhi(const BasicBlock &bb, const BasicBlock &from,
               bvop_details::Bv2OpSemContext &ctx);
  void execEdg(const BasicBlock &src, const BasicBlock &dst,
               bvop_details::Bv2OpSemContext &ctx);
  void execBr(const BasicBlock &src, const BasicBlock &dst,
              bvop_details::Bv2OpSemContext &ctx);

  void exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
            Expr act) override;
  void execPhi(SymStore &s, const BasicBlock &bb, const BasicBlock &from,
               ExprVector &side, Expr act) override;

  void execEdg(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
               ExprVector &side) override;

  void execBr(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
              ExprVector &side, Expr act) override;

  /**
     \brief Returns a symbolic expression corresponding to a value.
     If the value is a register, returns the corresponding symbolic register.

     If the value is a constant, returns a corresponding symbolic constant.

     If the value is a basic block, returns a symbolic Boolean
     register that is set to true whenever the block is executed.

     see also conc()
   */
  Expr symb(const Value &v) override;

  /**
     \brief Returns a concrete representation of a given symbolic
            expression. Assumes that the input expression has
            concrete representation.
   */
  const Value &conc(Expr v) override;

  /// \brief Indicates whether an instruction/value is skipped by
  /// the semantics. An instruction is skipped means that, from the
  /// perspective of the semantics, the instruction does not
  /// exist. It is not executed, has no effect on the execution
  /// context, and no instruction that is not skipped depends on it
  bool isSkipped(const Value &v);

  bool isTracked(const Value &v) override { return !isSkipped(v); }
  Expr memStart(unsigned id) override;
  Expr memEnd(unsigned id) override;

  /// \brief Returns true if the given expression is a symbolic register
  bool isSymReg(Expr v) override { llvm_unreachable(nullptr); }
  bool isSymReg(Expr v, bvop_details::Bv2OpSemContext &ctx);

  Expr mkSymbReg(const Value &v, OpSemContext &_ctx) override;

  Expr getOperandValue(const Value &v, bvop_details::Bv2OpSemContext &ctx);
  Expr lookup(SymStore &s, const Value &v) { llvm_unreachable(nullptr); }

  using gep_type_iterator = generic_gep_type_iterator<>;
  Expr symbolicIndexedOffset(gep_type_iterator it, gep_type_iterator end,
                             bvop_details::Bv2OpSemContext &ctx);

  unsigned storageSize(const llvm::Type *t) const;
  unsigned fieldOff(const StructType *t, unsigned field) const;

  uint64_t sizeInBits(const llvm::Value &v) const;
  uint64_t sizeInBits(const llvm::Type &t) const;
  unsigned pointerSizeInBits() const;

  /// Reports (and records) an instruction as skipped by the semantics
  void skipInst(const Instruction &inst, bvop_details::Bv2OpSemContext &ctx);
  /// Reports (and records) an instruction as not being handled by
  /// the semantics
  void unhandledInst(const Instruction &inst, bvop_details::Bv2OpSemContext &ctx);
  void unhandledValue(const Value &v, bvop_details::Bv2OpSemContext &ctx);

private:
  static bvop_details::Bv2OpSemContext &ctx(OpSemContext &_ctx);
};
} // namespace seahorn
