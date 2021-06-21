#pragma once

#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/OperationalSemantics.hh"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Pass.h"

#include <boost/container/flat_set.hpp>

// forward declarations
namespace llvm {
class GetElementPtrInst;
class LazyValueInfoWrapperPass;
} // namespace llvm

namespace clam {
class CrabBuilderManager;
class InterGlobalClam;
} // namespace clam

namespace seahorn {
namespace details {
class Bv2OpSemContext;
Bv2OpSemContext &ctx(OpSemContext &_ctx);
} // namespace details
/**
   Bit-precise operational semantics for LLVM (take 2)

   Fairly accurate representation of LLVM semantics without
   considering undefined behaviour. Most operators are mapped
   directly to their logical equivalent SMT-LIB representation.

   Memory is modelled by arrays.
 */
class Bv2OpSem : public OperationalSemantics {
  Pass &m_pass;
  TrackLevel m_trackLvl;

  const DataLayout *m_td;
  const TargetLibraryInfoWrapperPass *m_tliWrapper;
  const CanFail *m_canFail;

  /// \brief lvi's map used for analysis
  using lvi_func_map_t =
      DenseMap<const llvm::Function *, LazyValueInfoWrapperPass *>;
  std::unique_ptr<lvi_func_map_t> m_lvi_map;

  //// \brief crab's cfg builder manager
  std::unique_ptr<clam::CrabBuilderManager> m_cfg_builder_man;
  //// \brief crab instance to solve alloc bounds
  std::unique_ptr<clam::InterGlobalClam> m_crab_rng_solver;

public:
  Bv2OpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
           TrackLevel trackLvl = MEM);

  Bv2OpSem(const Bv2OpSem &o);

  ~Bv2OpSem();

  const DataLayout &getTD() {
    assert(m_td);
    return *m_td;
  }
  const DataLayout& getDataLayout() {return getTD();}

  /// \brief Creates a new context
  OpSemContextPtr mkContext(SymStore &values, ExprVector &side) override;

  /// \brief Executes one intra-procedural instructions in the
  /// current context. Assumes that current instruction is not a
  /// branch. Returns true if instruction was executed and false if
  /// there is no suitable instruction found
  bool intraStep(seahorn::details::Bv2OpSemContext &C);
  /// \brief Executes one intra-procedural branch instruction in the
  /// current context. Assumes that current instruction is a branch
  void intraBr(seahorn::details::Bv2OpSemContext &C, const BasicBlock &dst);

  /// \brief Execute all PHINode instructions of the current basic block
  /// \brief assuming that control flows from previous basic block
  void intraPhi(seahorn::details::Bv2OpSemContext &C);

  /// \brief Returns symbolic representation of the global errorFlag variable
  Expr errorFlag(const BasicBlock &BB) override;

  void exec(const BasicBlock &bb, OpSemContext &_ctx) override {
    exec(bb, details::ctx(_ctx));
  }
  void execPhi(const BasicBlock &bb, const BasicBlock &from,
               OpSemContext &_ctx) override {
    execPhi(bb, from, details::ctx(_ctx));
  }
  void execEdg(const BasicBlock &src, const BasicBlock &dst,
               OpSemContext &_ctx) override {
    execEdg(src, dst, details::ctx(_ctx));
  }
  void execBr(const BasicBlock &src, const BasicBlock &dst,
              OpSemContext &_ctx) override {
    execBr(src, dst, details::ctx(_ctx));
  }

protected:
  void exec(const BasicBlock &bb, seahorn::details::Bv2OpSemContext &ctx);
  void execPhi(const BasicBlock &bb, const BasicBlock &from,
               seahorn::details::Bv2OpSemContext &ctx);
  void execEdg(const BasicBlock &src, const BasicBlock &dst,
               seahorn::details::Bv2OpSemContext &ctx);
  void execBr(const BasicBlock &src, const BasicBlock &dst,
              seahorn::details::Bv2OpSemContext &ctx);

public:
  /// \brief Returns a concrete representation of a given symbolic expression.
  ///        Assumes that the input expression \p v has concrete representation.
  const Value &conc(Expr v) const override;

  /// \brief Indicates whether an instruction/value is skipped by
  /// the semantics. An instruction is skipped means that, from the
  /// perspective of the semantics, the instruction does not
  /// exist. It is not executed, has no effect on the execution
  /// context, and no instruction that is not skipped depends on it
  bool isSkipped(const Value &v) const;

  bool isTracked(const Value &v) const override { return !isSkipped(v); }

  /// \brief Deprecated. Returns true if \p v is a symbolic register
  bool isSymReg(Expr v) override { llvm_unreachable(nullptr); }
  /// \brief Returns true if \p v is a symbolic register
  bool isSymReg(Expr v, seahorn::details::Bv2OpSemContext &ctx);

  /// \brief Creates a symbolic register for an llvm::Value
  Expr mkSymbReg(const Value &v, OpSemContext &_ctx) override;
  /// \brief Finds a symbolic register for \p v, if it exists
  Expr getSymbReg(const Value &v, const OpSemContext &_ctx) const override;

  /// \brief Returns the current symbolic value of \p v in the context \p ctx
  Expr getOperandValue(const Value &v, seahorn::details::Bv2OpSemContext &ctx);
  /// \brief Deprecated
  Expr lookup(SymStore &s, const Value &v) { llvm_unreachable(nullptr); }
  /// Convert aggregate GenericValue to APInt
  Optional<APInt> agg(Type *ty, const std::vector<GenericValue> &elements,
      seahorn::details::Bv2OpSemContext &ctx);
  using gep_type_iterator = generic_gep_type_iterator<>;
  /// \brief Returns symbolic representation of the gep offset
  Expr symbolicIndexedOffset(gep_type_iterator it, gep_type_iterator end,
                             seahorn::details::Bv2OpSemContext &ctx);

  /// \brief Returns memory size of type \p t
  unsigned storageSize(const llvm::Type *t) const;
  /// \breif Returns offset of a filed in a structure
  unsigned fieldOff(const StructType *t, unsigned field) const;

  /// \brief Size of the register (in bits) required to store \p v 
  uint64_t sizeInBits(const llvm::Value &v) const;
  /// \brief Size of the register (in bits) required to store values of type \p t
  uint64_t sizeInBits(const llvm::Type &t) const;
  /// \brief Number of bits required to store a pointer
  unsigned pointerSizeInBits() const;

  /// Reports (and records) an instruction as skipped by the semantics
  void skipInst(const Instruction &inst,
                seahorn::details::Bv2OpSemContext &ctx);
  /// Reports (and records) an instruction as not being handled by
  /// the semantics
  void unhandledInst(const Instruction &inst,
                     seahorn::details::Bv2OpSemContext &ctx);
  void unhandledValue(const Value &v, seahorn::details::Bv2OpSemContext &ctx);

  /// \brief Creates a crab's cfg builder manager
  void initCrabAnalysis(const llvm::Module &M);
  /// \brief Run crab analysis
  void runCrabAnalysis();
  /// \brief Get the range of an instruction by crab
  const llvm::ConstantRange getCrabInstRng(const llvm::Instruction &I);
  /// \brief Run LVI analysis
  void runLVIAnalysis(const llvm::Function &F);
  /// \brief Get the range of an instruction by LVI
  const llvm::ConstantRange getLVIInstRng(llvm::Instruction &I);
};
} // namespace seahorn
