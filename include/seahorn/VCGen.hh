#pragma once
#include "seahorn/OperationalSemantics.hh"
#include "ufo/Smt/EZ3.hh"

namespace seahorn {
class CpEdge;
/**
 * Verification Condition (VC) generator for loop-free code.  Given
 * an operational semantics (OpSem) and loop-free code block,
 * generates a formula that encodes all executions through the code
 * block according to the given operational semantics.
 */
class VCGen {
  OperationalSemantics &m_sem;
  Expr trueE;

  /// \brief Generate VC for a basic block \p bb on the edge
  ///
  /// Helper method to generate a part of the VC corresponding for a given
  /// basic block on the edge
  void genVcForBasicBlockOnEdge(OpSemContext &ctx, const CpEdge &edge,
                                const BasicBlock &bb, bool last = false);

  /// \brief Initialize SMT solver for eager VC checking
  void initSmt(std::unique_ptr<ufo::EZ3> &zctx,
               std::unique_ptr<ufo::ZSolver<ufo::EZ3>> &smt);

  /// \brief Check consistency of side-condition up-to given block
  ///
  /// If the side-condition is unsat, the negation of the block
  /// variable is added to the condition
  void checkSideAtBb(unsigned &head, ExprVector &side, Expr bbV,
                     ufo::ZSolver<ufo::EZ3> &smt, const CpEdge &edg,
                     const BasicBlock &bb);

  /// \brief Check consistency of side condition at the last block
  ///
  /// If the side-condition is unsat, FALSE is added to the
  /// side-condition
  void checkSideAtEnd(unsigned &head, ExprVector &side,
                      ufo::ZSolver<ufo::EZ3> &smt);

public:
  VCGen(OperationalSemantics &sem) : m_sem(sem) {
    trueE = mk<TRUE>(m_sem.getExprFactory());
  }

  /// \brief Generate VC for a given edge in the CutPoint graph
  ///
  /// Returns a side-condition such that every satisfiable
  /// assignment of \p side corresponds to an execution through
  /// basic blocks in \p edge.
  ///
  /// Modifies symbolic store \p s to represent the state at the end
  /// of the edge
  virtual void genVcForCpEdgeLegacy(SymStore &s, const CpEdge &edge,
                              ExprVector &side);
  virtual void genVcForCpEdge(OpSemContext &ctx, const CpEdge &edge);
};
} // namespace seahorn
