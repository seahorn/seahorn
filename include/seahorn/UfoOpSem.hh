#pragma once
#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/LegacyOperationalSemantics.hh"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Pass.h"

#include "seahorn/VCGen.hh"

namespace llvm {
class GetElementPtrInst;
}

namespace seahorn {
/**
 * Operational semantics for LLVM based on one from UFO
 * This has evolved significantly from the original UFO semantics.
 *
 * All numeric types are represented by arbitrary precision integers
 * Memory is represented by arrays indexed by arbitrary precision integers
 *
 * This semantics is not very accurate. Should not be used for
 * low-level bit-precise reasoning.
 */
class UfoOpSem : public LegacyOperationalSemantics {
  Pass &m_pass;
  TrackLevel m_trackLvl;

public:
  typedef SmallPtrSet<const Function *, 8> FunctionPtrSet;

private:
  FunctionPtrSet m_abs_funcs;
  const DataLayout *m_td;
  const CanFail *m_canFail;

public:
  UfoOpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
           TrackLevel trackLvl = MEM, FunctionPtrSet abs_fns = FunctionPtrSet())
      : LegacyOperationalSemantics(efac), m_pass(pass), m_trackLvl(trackLvl), m_abs_funcs(abs_fns),
        m_td(&dl) {
    m_canFail = pass.getAnalysisIfAvailable<CanFail>();
  }
  UfoOpSem(const UfoOpSem &o)
      : LegacyOperationalSemantics(o), m_pass(o.m_pass), m_trackLvl(o.m_trackLvl),
        m_abs_funcs(o.m_abs_funcs), m_td(o.m_td), m_canFail(o.m_canFail) {}

  Expr errorFlag(const BasicBlock &BB) override;

  Expr memStart(unsigned id) override;
  Expr memEnd(unsigned id) override;

  void exec(SymStore &s, const BasicBlock &bb, ExprVector &side,
            Expr act) override;

  void execPhi(SymStore &s, const BasicBlock &bb, const BasicBlock &from,
               ExprVector &side, Expr act) override;

  void execEdg(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
               ExprVector &side) override;

  void execBr(SymStore &s, const BasicBlock &src, const BasicBlock &dst,
              ExprVector &side, Expr act) override;

  Expr symb(const Value &v) override;
  const Value &conc(Expr v) const override;
  bool isTracked(const Value &v) const override;
  Expr lookup(SymStore &s, const Value &v) override;
  bool isAbstracted(const Function &fn) override;
  Expr ptrArith(SymStore &s, llvm::GetElementPtrInst &gep);
  unsigned storageSize(const llvm::Type *t);
  unsigned fieldOff(const StructType *t, unsigned field);
};

} // namespace seahorn
