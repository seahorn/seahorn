#ifndef __UFO_SYM_EXEC_HH_
#define __UFO_SYM_EXEC_HH_

#include "llvm/Pass.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/DataLayout.h"
#include "seahorn/SymExec.hh"
#include "seahorn/Analysis/CanFail.hh"

namespace seahorn
{
  /// Small step symbolic execution for integers based on UFO semantics
  class UfoSmallSymExec : public SmallStepSymExec
  { 
    Pass &m_pass;
    TrackLevel m_trackLvl;

  public:    
    typedef SmallPtrSet<const Function *, 8> FunctionPtrSet;
    
  private:
    FunctionPtrSet m_abs_funcs;
    const DataLayout *m_td;
    const CanFail *m_canFail;
        
  public:
    UfoSmallSymExec (ExprFactory &efac, Pass &pass,
		     TrackLevel trackLvl = MEM,
		     FunctionPtrSet abs_fns = FunctionPtrSet ()) : 
      SmallStepSymExec (efac), m_pass (pass),
      m_trackLvl (trackLvl), m_abs_funcs (abs_fns)
    {
      m_td = &pass.getAnalysis<DataLayoutPass> ().getDataLayout ();
      m_canFail = pass.getAnalysisIfAvailable<CanFail> ();
    }
    UfoSmallSymExec (const UfoSmallSymExec& o) : 
      SmallStepSymExec (o), m_pass (o.m_pass),
      m_trackLvl (o.m_trackLvl), m_abs_funcs (o.m_abs_funcs) {}
    
    Expr errorFlag (const BasicBlock &BB) override;

    virtual Expr memStart (unsigned id); 
    virtual Expr memEnd (unsigned id); 
    
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
    
    virtual Expr symb (const Value &v);
    virtual const Value &conc (Expr v);
    virtual bool isTracked (const Value &v);
    virtual Expr lookup (SymStore &s, const Value &v);
    virtual bool isAbstracted (const Function& fn);
    Expr ptrArith (SymStore &s, const Value& base, 
                   SmallVectorImpl<const Value*> &ps,
                   SmallVectorImpl<const Type *> &ts);
    unsigned storageSize (const llvm::Type *t);
    unsigned fieldOff (const StructType *t, unsigned field);
  }; 
  

  class UfoLargeSymExec : public LargeStepSymExec
  {
    SmallStepSymExec &m_sem;
    Expr trueE;
    
    void execEdgBb (SymStore &s, const CpEdge &edge, 
                    const BasicBlock &bb, ExprVector &side, bool last = false);
    
  public:
    UfoLargeSymExec (SmallStepSymExec &sem)
      : m_sem (sem) { trueE = mk<TRUE> (m_sem.getExprFactory ()); }
    
    virtual void execCpEdg (SymStore &s, const CpEdge &edge, ExprVector &side);
    
    
  };  
}

#endif
