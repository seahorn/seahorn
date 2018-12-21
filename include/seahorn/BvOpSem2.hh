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
class OpSemMemManager;
}

class Bv2OpSemContext : public OpSemContext {
public:
  /// currently executing function
  const Function *m_func;
  /// currently executing basic block
  const BasicBlock *m_bb;
  /// the next instruction to be executed
  BasicBlock::const_iterator m_inst;

  /// Previous basic block (if known)
  const BasicBlock *m_prev;

  /// Meta register that contains the name of the register to be
  /// used in next memory load
  Expr m_readRegister;
  /// Meta register that contains the name of the register to be
  /// used in next memory store
  Expr m_writeRegister;
  /// true if current in/out memory is a unique scalar memory cell
  bool m_scalar;

  /// Parameters for the current function call
  ExprVector m_fparams;

  /// Instructions that where ignored by the semantics
  DenseSet<const Instruction *> m_ignored;

  /// \brief Declared symbolic registers
  boost::container::flat_set<Expr> m_registers;

  std::unique_ptr<bvop_details::OpSemMemManager> m_memManager;

  Bv2OpSemContext(SymStore &values, ExprVector &side);
  Bv2OpSemContext(SymStore &values, ExprVector &side,
                  const Bv2OpSemContext &other);
  Bv2OpSemContext(const Bv2OpSemContext &) = delete;
  ~Bv2OpSemContext() override;

  void setMemManager(bvop_details::OpSemMemManager *man);
  bvop_details::OpSemMemManager *getMemManager() { return m_memManager.get(); }

  void pushParameter(Expr v) { m_fparams.push_back(v); }
  void setParameter(unsigned idx, Expr v) { m_fparams[idx] = v; }
  void resetParameters() { m_fparams.clear(); }
  ExprVector &getParameters() { return m_fparams; }

  void setMemReadRegister(Expr r) { m_readRegister = r; }
  Expr getMemReadRegister() { return m_readRegister; }
  void setMemWriteRegister(Expr r) { m_writeRegister = r; }
  Expr getMemWriteRegister() { return m_writeRegister; }
  bool isMemScalar() { return m_scalar; }
  void setMemScalar(bool v) { m_scalar = v; }

  Expr loadValueFromMem(Expr ptr, const llvm::Type &ty, uint32_t align);
  Expr storeValueToMem(Expr val, Expr ptr, const llvm::Type &ty,
                       uint32_t align);
  Expr MemSet(Expr ptr, Expr val, unsigned len, uint32_t align);

  /// \brief Called when a module is entered
  void onModuleEntry(const Module &M) override;
  /// \brief Called when a function is entered
  void onFunctionEntry(const Function &fn) override;
  /// \brief Called when a function returns
  void onFunctionExit(const Function &fn) override {}

  /// \brief Call when a basic block is entered
  void onBasicBlockEntry(const BasicBlock &bb) override {
    if (!m_func)
      m_func = bb.getParent();
    assert(m_func == bb.getParent());
    if (m_bb)
      m_prev = m_bb;
    m_bb = &bb;
    m_inst = bb.begin();
  }

  void declareRegister(Expr v);
  bool isKnownRegister(Expr v);

  OpSemContextPtr fork(SymStore &values, ExprVector &side) {
    return OpSemContextPtr(new Bv2OpSemContext(values, side, *this));
  }

private:
  Bv2OpSemContext &ctx(OpSemContext &ctx) {
    return static_cast<Bv2OpSemContext &>(ctx);
  }
};

namespace bvop_details {
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

  Pass &m_pass;
  TrackLevel m_trackLvl;

  const DataLayout *m_td;
  const TargetLibraryInfo *m_tli;
  const CanFail *m_canFail;

  /// Useful constants
  Expr trueE;
  Expr falseE;
  Expr zeroE;
  Expr oneE;
  Expr trueBv;
  Expr falseBv;
  Expr nullBv;
  /// MAX_PTR value
  Expr maxPtrE;

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

  OpSemContextPtr mkContext(SymStore &values, ExprVector &side) override {
    return OpSemContextPtr(new Bv2OpSemContext(values, side));
  }
  /// \brief Executes one intra-procedural instructions in the
  /// current context Assumes that current instruction is not a
  /// branch Returns true if instruction was executed and false if
  /// there is no suitable instruction found
  bool intraStep(Bv2OpSemContext &C);
  /// \brief Executes one intra-procedural branch instruction in the
  /// current context. Assumes that current instruction is a branch
  void intraBr(Bv2OpSemContext &C, const BasicBlock &dst);

  /// \brief Execute all PHINode instructions of the current basic block
  /// \brief assuming that control flows from previous basic block
  void intraPhi(Bv2OpSemContext &C);

  Expr errorFlag(const BasicBlock &BB) override;

  Bv2OpSemContext &ctx(OpSemContext &_ctx) {
    return static_cast<Bv2OpSemContext &>(_ctx);
  }
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

  void exec(const BasicBlock &bb, Bv2OpSemContext &ctx);
  void execPhi(const BasicBlock &bb, const BasicBlock &from,
               Bv2OpSemContext &ctx);
  void execEdg(const BasicBlock &src, const BasicBlock &dst,
               Bv2OpSemContext &ctx);
  void execBr(const BasicBlock &src, const BasicBlock &dst,
              Bv2OpSemContext &ctx);

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
  bool isSymReg(Expr v, Bv2OpSemContext &ctx);

  Expr getOperandValue(const Value &v, Bv2OpSemContext &ctx);
  Expr lookup(SymStore &s, const Value &v) { llvm_unreachable(nullptr); }

  using gep_type_iterator = generic_gep_type_iterator<>;
  Expr symbolicIndexedOffset(gep_type_iterator it, gep_type_iterator end,
                             Bv2OpSemContext &ctx);

  unsigned storageSize(const llvm::Type *t) const;
  unsigned fieldOff(const StructType *t, unsigned field) const;

  uint64_t sizeInBits(const llvm::Value &v) const;
  uint64_t sizeInBits(const llvm::Type &t) const;
  unsigned pointerSizeInBits() const;

  /// Reports (and records) an instruction as skipped by the semantics
  void skipInst(const Instruction &inst, Bv2OpSemContext &ctx);
  /// Reports (and records) an instruction as not being handled by
  /// the semantics
  void unhandledInst(const Instruction &inst, Bv2OpSemContext &ctx);
  void unhandledValue(const Value &v, Bv2OpSemContext &ctx);

  Expr boolToBv(Expr b);
  Expr bvToBool(Expr bv);
};
} // namespace seahorn
