#pragma once
// This is a copy of UfoOpSem for prototyping purposes

#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/LegacyOperationalSemantics.hh"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Pass.h"

#include "seahorn/VCGen.hh"
#include "seahorn/UfoOpSem.hh"

#include "sea_dsa/ShadowMem.hh"
#include "seahorn/InterMemPreProc.hh"

namespace dsa = sea_dsa;

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
class UfoOpMemSem : public LegacyOperationalSemantics {
  Pass &m_pass;
  TrackLevel m_trackLvl;

public:
  typedef UfoOpSem::FunctionPtrSet FunctionPtrSet;
  ShadowMem *m_shadowDsa;
  std::shared_ptr<InterMemPreProc> m_preproc = nullptr;

private:
  FunctionPtrSet m_abs_funcs;
  const DataLayout *m_td;
  const CanFail *m_canFail;

public :
  UfoOpMemSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
              std::shared_ptr<InterMemPreProc> preproc, TrackLevel trackLvl = MEM,
              FunctionPtrSet abs_fns = FunctionPtrSet(),
              ShadowMem *dsa = NULL)
      : LegacyOperationalSemantics(efac), m_pass(pass), m_trackLvl(trackLvl),
        m_abs_funcs(abs_fns), m_td(&dl), m_shadowDsa(dsa),
        m_preproc(preproc) {
    m_canFail = pass.getAnalysisIfAvailable<CanFail>();
  }
  UfoOpMemSem(const UfoOpMemSem &o)
      : LegacyOperationalSemantics(o), m_pass(o.m_pass),
        m_trackLvl(o.m_trackLvl), m_abs_funcs(o.m_abs_funcs), m_td(o.m_td),
        m_canFail(o.m_canFail), m_shadowDsa(o.m_shadowDsa),
        m_preproc(o.m_preproc) {}

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
