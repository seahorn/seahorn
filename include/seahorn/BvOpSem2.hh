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


    /// Current memory region for loads/reads
    Expr m_inMem;
    /// Current memory region for stores/writes
    Expr m_outMem;
    /// true if current in/out memory is a unique scalar memory cell
    bool m_uniq;

    /// Parameters for the current function call
    ExprVector m_fparams;

    /// Instructions that where ignored by the semantics
    DenseSet<const Instruction*> m_ignored;

    OpSemContext(SymStore &values, ExprVector &side) :
      m_func(nullptr), m_bb(nullptr), m_inst(nullptr),
      m_values(values), m_side(side), m_prev(nullptr), m_uniq(false) {}

    void regParam(Expr v) {m_fparams.push_back(v);}
    void resetParams() {m_fparams.clear();}

    void addSideSafe(Expr v) { m_side.push_back(boolop::limp(m_act, v)); }
    void addSide(Expr v) {m_side.push_back(v);}
    void addDef(Expr v, Expr u) {addSide(mk<EQ>(v, u));}
    void addDefSafe(Expr v, Expr u) {addSideSafe(mk<EQ>(v,u));}
    void resetSide() {m_side.clear();}
    Expr read(Expr v) {return m_values.read(v);}

    ExprFactory &getExprFactory() const {return m_values.getExprFactory();}
    void update_bb(const BasicBlock &bb) {
      if (!m_func) m_func = bb.getParent();
      assert(m_func == bb.getParent());
      if (m_bb) m_prev = m_bb;
      m_bb = &bb;
      m_inst = bb.begin();
    }
  };

  namespace bvop_details {
    class OpSemBase;
    class OpSemVisitor;
    class OpSemPhiVisitor;
  }
  /**
     Bit-precise operational semantics for LLVM (take 2)

     Fairly accurate representation of LLVM semantics without
     considering undefined behaviour. Most operators are mapped
     directly to their logical equivalent SMT-LIB representation.

     Memory is modelled by arrays.
   */
  class Bv2OpSem : public OpSem
  {
    friend class bvop_details::OpSemBase;
    friend class bvop_details::OpSemVisitor;
    friend class bvop_details::OpSemPhiVisitor;

    Pass &m_pass;
    TrackLevel m_trackLvl;

    const DataLayout *m_td;
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
    Bv2OpSem (ExprFactory &efac, Pass &pass, const DataLayout &dl,
              TrackLevel trackLvl = MEM);

    Bv2OpSem (const Bv2OpSem& o);

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

    /**
       \brief Returns a symbolic expression corresponding to a value.
       If the value is a register, returns the corresponding symbolic register.

       If the value is a constant, returns a corresponding symbolic constant.

       If the value is a basic block, returns a symbolic Boolean
       register that is set to true whenever the block is executed.

       see also conc()
     */
    Expr symb (const Value &v) override;

    /**
       \brief Returns a concrete representation of a given symbolic
              expression. Assumes that the input expression has
              concrete representation.
     */
    const Value &conc (Expr v) override;

    /// \brief Indicates whether an instruction/value is skipped by
    /// the semantics. An instruction is skipped means that, from the
    /// perspective of the semantics, the instruction does not
    /// exist. It is not executed, has no effect on the execution
    /// context, and no instruction that is not skipped depends on it
    bool isSkipped(const Value &v);


    /// \brief Returns true if the given expression is a symbolic register
    bool isSymReg(Expr v);

    Expr getOperandValue(const Value &v, OpSemContext &ctx);
    Expr lookup (SymStore &s, const Value &v) {llvm_unreachable(nullptr);}

    Expr symbolicIndexedOffset (SymStore &s, llvm::GetElementPtrInst& gep);
    unsigned storageSize (const llvm::Type *t) const;
    unsigned fieldOff (const StructType *t, unsigned field) const;

    uint64_t sizeInBits (const llvm::Value &v) const;
    uint64_t sizeInBits (const llvm::Type &t) const;
    unsigned pointerSizeInBits () const;

    /// Reports (and records) an instruction as skipped by the semantics
    void skipInst(const Instruction &inst, OpSemContext &ctx);
    /// Reports (and records) an instruction as not being handled by
    /// the semantics
    void unhandledInst(const Instruction &inst, OpSemContext &ctx);
    void unhandledValue(const Value &v, OpSemContext &ctx);
  };
}
