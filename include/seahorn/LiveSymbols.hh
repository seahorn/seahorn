#ifndef __LIVE_SYMBOLS__HH_
#define __LIVE_SYMBOLS__HH_

#include "llvm/ADT/DenseMap.h"
#include "llvm/IR/Function.h"

#include "seahorn/OperationalSemantics.hh"
#include "seahorn/SymStore.hh"
#include "seahorn/Expr/Expr.hh"

namespace seahorn {
using namespace llvm;
using namespace expr;

class LiveInfo {
  ExprVector m_live;
  ExprVector m_defs;
  llvm::SmallVector<ExprVector, 16> m_edgeDefs;

public:
  LiveInfo() {}
  LiveInfo(const LiveInfo &o)
      : m_live(o.m_live), m_defs(o.m_defs), m_edgeDefs(o.m_edgeDefs) {}

  LiveInfo &operator=(LiveInfo o) {
    std::swap(m_live, o.m_live);
    std::swap(m_defs, o.m_defs);
    std::swap(m_edgeDefs, o.m_edgeDefs);
    return *this;
  }

  void setLive(const ExprVector &l);
  void setDefs(const ExprVector &d);
  void addEdgeDef(const ExprVector &d);
  /// add live variables. These should not be already live
  void addLive(ExprVector &v);
  /// like addLive but v can contain variables already live
  void unionLive(ExprVector &v);

  const ExprVector &live() const { return m_live; }
  const ExprVector &defs() const { return m_defs; }
  const ExprVector &edge_defs(unsigned i) const { return m_edgeDefs[i]; }
};

/// Computes the set of live symbols (variables) at every BasicBlock
/// of a function. Parameterized by the symbolic execution semantics.
class LiveSymbols {
  const Function &m_f;
  ExprFactory &m_efac;

  OperationalSemantics &m_sem;
  ExprVector m_side;

  std::vector<const BasicBlock *> m_rtopo;

  SymStore m_gstore;
  DenseMap<const BasicBlock *, LiveInfo> m_liveInfo;
  Expr trueE;

  void symExec(OpSemContext &ctx, const BasicBlock &bb);
  void symExecPhi(OpSemContext &ctx, const BasicBlock &bb,
                  const BasicBlock &from);

  /// -- compute live info based on what is used in each individual basic block
  void localPass();
  /// -- extend Args and Globals used in the function to be live throughout
  void patchArgsAndGlobals();
  /// -- compute global live info by propagating local live info
  void globalPass();

public:
  LiveSymbols(const Function &F, ExprFactory &efac, OperationalSemantics &semantics)
      : m_f(F), m_efac(efac), m_sem(semantics), m_gstore(efac) {
    trueE = mk<TRUE>(m_efac);
  }

  LiveSymbols(const LiveSymbols &o)
      : m_f(o.m_f), m_efac(o.m_efac), m_sem(o.m_sem), m_side(),
        m_rtopo(o.m_rtopo), m_gstore(o.m_gstore), m_liveInfo(o.m_liveInfo),
        trueE(o.trueE) {}

  void run();
  void operator()() { run(); }
  /// Add additional globally live symbols
  void globallyLive(ExprVector &live);
  const ExprVector &live(const BasicBlock *bb) const;
  void dump() const;
};

} // namespace seahorn

#endif
