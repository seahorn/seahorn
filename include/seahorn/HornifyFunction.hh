#ifndef __HORNIFY_FUNCTION__HH_
#define __HORNIFY_FUNCTION__HH_

#include "seahorn/HornifyModule.hh"
#include "llvm/IR/Function.h"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/LiveSymbols.hh"
#include "seahorn/UfoOpSem.hh"

/// Constructs Horn clauses for a single function

namespace {

/// Find a function exit basic block.  Assumes that the function has
/// a unique block with return instruction
inline const llvm::BasicBlock *findExitBlock(const llvm::Function &F) {
  for (const llvm::BasicBlock &bb : F)
    if (llvm::isa<llvm::ReturnInst>(bb.getTerminator()))
      return &bb;
  return nullptr;
}

} // namespace

namespace seahorn {
using namespace expr;
using namespace llvm;

class HornifyFunction {
protected:
  HornifyModule &m_parent;

  LegacyOperationalSemantics &m_sem;
  HornClauseDB &m_db;
  EZ3 &m_zctx;
  ExprFactory &m_efac;

  llvm::Function *m_synthAssertFn = nullptr;

  /// whether encoding is inter-procedural (i.e., with summaries)
  bool m_interproc;

  void extractFunctionInfo(const BasicBlock &BB);

  llvm::SmallVector<llvm::Instruction *, 8> getPartialFnsToSynth(Function &F);
  void expandEdgeFilter(llvm::Instruction &I);

public:
  HornifyFunction(HornifyModule &parent, bool interproc = false)
      : m_parent(parent), m_sem(m_parent.symExec()),
        m_db(m_parent.getHornClauseDB()), m_zctx(parent.getZContext()),
        m_efac(m_zctx.getExprFactory()), m_interproc(interproc) {}

  virtual ~HornifyFunction() {}
  HornClauseDB &getHornClauseDB() { return m_db; }
  virtual void runOnFunction(Function &F) = 0;
  // bool checkProperty(ExprVector prop, Expr &inv);
};

class SmallHornifyFunction : public HornifyFunction {
  void mkBBSynthRules(const LiveSymbols &ls, Function &F, SymStore &store);

public:
  SmallHornifyFunction(HornifyModule &parent, bool interproc = false)
      : HornifyFunction(parent, interproc) {}

  virtual void runOnFunction(Function &F);
};

class LargeHornifyFunction : public HornifyFunction {
public:
  LargeHornifyFunction(HornifyModule &parent, bool interproc = false)
      : HornifyFunction(parent, interproc) {}

  virtual void runOnFunction(Function &F);
};

} // namespace seahorn

#endif
