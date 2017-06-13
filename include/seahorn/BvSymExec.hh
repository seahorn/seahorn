#ifndef __BV_SYM_EXEC_HH_
#define __BV_SYM_EXEC_HH_

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"
#include "seahorn/SymExec.hh"
#include "seahorn/Analysis/CanFail.hh"

namespace seahorn
{
  
  /// Integer abstraction of a bv-expression
  /// Assumes the input is in nnf
  Expr bvIntAbstract (Expr v);
  
  
  /// Bit-Vector Symbolic Execution
  class BvSmallSymExec : public SmallStepSymExec
  { 
    Pass &m_pass;
    TrackLevel m_trackLvl;
   
    const DataLayout *m_td;
    const CanFail *m_canFail;
    
    
  public:
    BvSmallSymExec (ExprFactory &efac, Pass &pass, const DataLayout &dl,
		    TrackLevel trackLvl = MEM) : 
      SmallStepSymExec (efac), m_pass (pass), m_trackLvl (trackLvl), m_td(&dl)
    {
      m_canFail = pass.getAnalysisIfAvailable<CanFail> ();
    }
    BvSmallSymExec (const BvSmallSymExec& o) : 
      SmallStepSymExec (o), m_pass (o.m_pass), m_trackLvl (o.m_trackLvl),
      m_td (o.m_td), m_canFail (o.m_canFail) {}
    
    Expr errorFlag (const BasicBlock &BB) override;
    
    virtual void exec (SymStore &s, const BasicBlock &bb, 
                       ExprVector &side, Expr act);
    
    virtual void exec (SymStore &s, const Instruction &inst, 
                       ExprVector &side);
    
    virtual void execPhi (SymStore &s, const BasicBlock &bb, 
                          const BasicBlock &from, ExprVector &side, Expr act);
    
    virtual void execEdg (SymStore &s, const BasicBlock &src,
                          const BasicBlock &dst, ExprVector &side);
    
    virtual void execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                         ExprVector &side, Expr act);

    virtual Expr memStart (unsigned id);
    virtual Expr memEnd (unsigned id);
    
    virtual Expr symb (const Value &v);
    virtual const Value &conc (Expr v);
    virtual bool isTracked (const Value &v);
    virtual Expr lookup (SymStore &s, const Value &v);
    
    Expr symbolicIndexedOffset (SymStore &s,
                                Type *ptrTy,
                                ArrayRef<Value *> Indicies);
    unsigned storageSize (const llvm::Type *t) const;
    unsigned fieldOff (const StructType *t, unsigned field) const;

    uint64_t sizeInBits (const llvm::Value &v) const;
    uint64_t sizeInBits (const llvm::Type &t) const;
    unsigned pointerSizeInBits () const;
  }; 
}

#endif
