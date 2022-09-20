#pragma once
/* Based on a copy-and-paste version of UfoOpSem */

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"
#include "seahorn/LegacyOperationalSemantics.hh"
#include "seahorn/Analysis/CanFail.hh"

namespace llvm {
  class GetElementPtrInst;
}

namespace seahorn
{

  /**
     LLVM operational semantics that can be well represented in CLP

     Very imprecise/inaccurate. Only interesting for comparing with
     CLP-based analysis tools.
  */
  class ClpOpSem : public LegacyOperationalSemantics
  {
    Pass &m_pass;
    TrackLevel m_trackLvl;

    const DataLayout *m_td;
    const CanFail *m_canFail;

    Expr zero;
    Expr one;

  public:
    ClpOpSem (ExprFactory &efac, Pass &pass, const DataLayout &dl,
		     TrackLevel trackLvl = MEM) :
      LegacyOperationalSemantics (efac), m_pass (pass), m_trackLvl (trackLvl), m_td(&dl)
    {
      m_canFail = pass.getAnalysisIfAvailable<CanFail> ();
      zero = mkTerm<expr::mpz_class>(0UL, m_efac);
      one  = mkTerm<expr::mpz_class>(1UL, m_efac);
    }

    ClpOpSem (const ClpOpSem& o) :
      LegacyOperationalSemantics (o), m_pass (o.m_pass), m_trackLvl (o.m_trackLvl),
      m_td (o.m_td), m_canFail (o.m_canFail) {}

    Expr errorFlag (const BasicBlock &BB) override;
    virtual Expr memStart (unsigned id) override { assert (false); return Expr (); }
    virtual Expr memEnd (unsigned id) override { assert (false); return Expr (); }

    virtual void exec (SymStore &s, const BasicBlock &bb,
                       ExprVector &side, Expr act) override;

    using LegacyOperationalSemantics::exec;
    virtual void exec (SymStore &s, const Instruction &inst,
                       ExprVector &side);

    virtual void execPhi (SymStore &s, const BasicBlock &bb,
                          const BasicBlock &from, ExprVector &side, Expr act) override;

    virtual void execEdg (SymStore &s, const BasicBlock &src,
                          const BasicBlock &dst, ExprVector &side) override;

    virtual void execBr (SymStore &s, const BasicBlock &src, const BasicBlock &dst,
                         ExprVector &side, Expr act) override;

    virtual Expr symb (const Value &v) override;
    virtual const Value &conc (Expr v) const override;
    virtual bool isTracked (const Value &v) const override;
    virtual Expr lookup (SymStore &s, const Value &v) override;
    Expr ptrArith (SymStore &s, llvm::GetElementPtrInst& gep);
    unsigned storageSize (const llvm::Type *t);
    unsigned fieldOff (const StructType *t, unsigned field);
  };

}
