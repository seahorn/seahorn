#ifndef __CLP_SYM_EXEC_HH_
#define __CLP_SYM_EXEC_HH_

/* Based on a copy-and-paste version of UfoSymExec */

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"
#include "seahorn/SymExec.hh"
#include "seahorn/Analysis/CanFail.hh"

namespace seahorn
{
  
  /// Small step symbolic execution for integers based on CLP semantics
  class ClpSmallSymExec : public SmallStepSymExec
  { 
    Pass &m_pass;
    TrackLevel m_trackLvl;
   
    const DataLayout *m_td;
    const CanFail *m_canFail;

    Expr zero;
    Expr one;
    
  public:
    ClpSmallSymExec (ExprFactory &efac, Pass &pass, const DataLayout &dl,
		     TrackLevel trackLvl = MEM) : 
      SmallStepSymExec (efac), m_pass (pass), m_trackLvl (trackLvl), m_td(&dl)
    {
      m_canFail = pass.getAnalysisIfAvailable<CanFail> ();
      zero = mkTerm<mpz_class> (0, m_efac);
      one  = mkTerm<mpz_class> (1, m_efac);
    }

    ClpSmallSymExec (const ClpSmallSymExec& o) : 
      SmallStepSymExec (o), m_pass (o.m_pass), m_trackLvl (o.m_trackLvl),
      m_td (o.m_td), m_canFail (o.m_canFail) {}
    
    Expr errorFlag (const BasicBlock &BB) override;
    virtual Expr memStart (unsigned id) { assert (false); return Expr (); }
    virtual Expr memEnd (unsigned id) { assert (false); return Expr (); }
    
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
    
    Expr ptrArith (SymStore &s, const Value& base, 
                   SmallVectorImpl<const Value*> &ps,
                   SmallVectorImpl<const Type *> &ts);
    unsigned storageSize (const llvm::Type *t);
    unsigned fieldOff (const StructType *t, unsigned field);
  }; 
  
}

#endif
