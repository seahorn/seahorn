#pragma once

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/ExecutionEngine/GenericValue.h"
#include "seahorn/OpSem.hh"
#include "seahorn/Analysis/CanFail.hh"

namespace llvm {
  class GetElementPtrInst;
}

namespace seahorn
{

  struct OpSemContext {
    /// currently executing function
    const Function *m_func;
    /// currently executing basic block
    const BasicBlock *m_bb;
    /// the next instruction to be executed
    BasicBlock::const_iterator m_inst;
    /// A map from symbolic registers to symbolic values
    /// XXX for now lives outside of the context
    SymStore &m_values;

    /// Side-condition to keep extra constraints (e.g., path condition)
    /// XXX for now lives outside of the context
    ExprVector& m_side;

    /// Activation literal for protecting conditions
    Expr m_act;

    /// Previous basic block (if known)
    const BasicBlock *m_prev;

    OpSemContext(SymStore &values, ExprVector &side) :
      m_func(nullptr), m_bb(nullptr), m_inst(nullptr),
      m_values(values), m_side(side), m_prev(nullptr) {}

    void add_side_safe(Expr v) { boolop::limp(m_act, v); }
    void reset_side() {m_side.clear();}
    Expr read(Expr v) {return m_values.read(v);}

    void update_bb(const BasicBlock &bb) {
      if (!m_func) m_func = bb.getParent();
      assert(m_func == bb.getParent());
      if (m_bb) m_prev = m_bb;
      m_bb = &bb;
      m_inst = bb.begin();
    }
  };

  /**
     Bit-precise operational semantics for LLVM (take 2)

     Fairly accurate representation of LLVM semantics without
     considering undefined behaviour. Most operators are mapped
     directly to their logical equivalent SMT-LIB representation.

     Memory is modelled by arrays.
   */
  class Bv2OpSem : public OpSem
  {
    Pass &m_pass;
    TrackLevel m_trackLvl;

    const DataLayout *m_td;
    const CanFail *m_canFail;

    /// Evaluates constant expression into a value
    Optional<GenericValue> getConstantValue(const Constant *C);

  public:
    Bv2OpSem (ExprFactory &efac, Pass &pass, const DataLayout &dl,
             TrackLevel trackLvl = MEM) :
      OpSem (efac), m_pass (pass), m_trackLvl (trackLvl), m_td(&dl)
    {m_canFail = pass.getAnalysisIfAvailable<CanFail> ();}

    Bv2OpSem (const Bv2OpSem& o) :
      OpSem (o), m_pass (o.m_pass), m_trackLvl (o.m_trackLvl),
      m_td (o.m_td), m_canFail (o.m_canFail) {}

    /// \brief Executes one intra-procedural instructions in the
    /// current context Assumes that current instruction is not a
    /// branch Returns true if instruction was executed and false if
    /// there is no suitable instruction found
    bool intraStep(OpSemContext &C);
    /// \brief Executes one intra-procedural branch instruction in the
    /// current context. Assumes that current instruction is a branch
    void intraBr(OpSemContext &C, const BasicBlock &dst);

    /// \brief Execute all PHINode instructions of the current basic block
    /// \brief assuming that control flows from previous basic block
    void intraPhi(OpSemContext &C);

    Expr errorFlag (const BasicBlock &BB) override;

    void exec (SymStore &s, const BasicBlock &bb,
               ExprVector &side, Expr act) override;

    void exec (SymStore &s, const Instruction &inst,
                       ExprVector &side) override;

    void execPhi (SymStore &s, const BasicBlock &bb,
                  const BasicBlock &from, ExprVector &side, Expr act) override;

    void execEdg (SymStore &s, const BasicBlock &src,
                  const BasicBlock &dst, ExprVector &side) override;

    void execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                 ExprVector &side, Expr act) override;

    virtual Expr memStart (unsigned id);
    virtual Expr memEnd (unsigned id);

    virtual Expr symb (const Value &v);
    virtual const Value &conc (Expr v);
    virtual bool isTracked (const Value &v);
    virtual Expr lookup (SymStore &s, const Value &v);

    Expr symbolicIndexedOffset (SymStore &s, llvm::GetElementPtrInst& gep);
    unsigned storageSize (const llvm::Type *t) const;
    unsigned fieldOff (const StructType *t, unsigned field) const;

    uint64_t sizeInBits (const llvm::Value &v) const;
    uint64_t sizeInBits (const llvm::Type &t) const;
    unsigned pointerSizeInBits () const;
  };
}
