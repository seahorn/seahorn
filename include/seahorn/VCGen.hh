#pragma once
#include "seahorn/OperationalSemantics.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

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
  void initSmt(std::unique_ptr<EZ3> &zctx,
               std::unique_ptr<ZSolver<EZ3>> &smt);

  /// \brief Check consistency of side-condition up-to a given basic block
  ///
  /// If the side-condition is unsat, the negation of the block
  /// variable is added to the condition
  /// \param head
  /// \param side the side condition
  /// \param pathCond the path condition for \p bb
  /// \param smt an smt solver to use for the check
  /// \param edg the cut-point edge
  /// \param bb the basic block at which side-condition is checked
  void checkSideAtBb(unsigned &head, ExprVector &side, Expr pathCond,
                     ZSolver<EZ3> &smt, const CpEdge &edg,
                     const BasicBlock &bb);

  /// \brief Check consistency of side condition at the last block
  ///
  /// If the side-condition is unsat, FALSE is added to the
  /// side-condition
  void checkSideAtEnd(unsigned &head, ExprVector &side,
                      ZSolver<EZ3> &smt);

public:
  VCGen(OperationalSemantics &sem) : m_sem(sem) {
    trueE = mk<TRUE>(m_sem.getExprFactory());
  }

  /// \brief Generate VC for a given edge in the CutPoint graph
  ///
  /// Constructs a logical formula \p side such that every satisfiable
  /// assignment of \p side corresponds to an execution through
  /// the basic blocks in \p edge.
  ///
  /// Modifies symbolic store \p s to represent the state at the end
  /// of the edge.
  virtual void genVcForCpEdgeLegacy(SymStore &s, const CpEdge &edge,
                              ExprVector &side);

  /// \brief Computes VC for an edge in a cut-point graph
  ///
  /// Computes a Verification Condition (VC) for a cut-point graph edge \p edge.
  /// The computation affects the \p OpSemContext \p ctx. The final VC is
  /// accessible via \p ctx.side()
  virtual void genVcForCpEdge(OpSemContext &ctx, const CpEdge &edge);
};
} // namespace seahorn
