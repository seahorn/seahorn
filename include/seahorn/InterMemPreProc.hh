#pragma once

#include "seadsa/CompleteCallGraph.hh"
#include "seadsa/DsaColor.hh"
#include "seadsa/Mapper.hh"
#include "seadsa/ShadowMem.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/LegacyOperationalSemantics.hh"

namespace seahorn {

struct CellInfo {
  unsigned m_nks = 0;
  unsigned m_nacss = 0;
  expr::ExprVector m_ks;
};

using CellKeysMap =
    llvm::DenseMap<const seadsa::Node *,
                   std::unordered_map<unsigned, expr::ExprVector>>;

using CellExprMap = DenseMap<std::pair<const seadsa::Node *, unsigned>, Expr>;

// preprocesor for vcgen with memory copies
class InterMemPreProc {
  /*! \brief Keeps for each CallSite of a module the simulation relation
   * between the caller and the callee (context sensitive), the nodes that
   * unsafe to copy per callee, caller and function (context insensitive).
   */
private:
  seadsa::CompleteCallGraph &m_ccg;
  seadsa::ShadowMem &m_shadowDsa;

  using SimMapperCSMap =
      llvm::DenseMap<const llvm::Instruction *, seadsa::SimulationMapper>;
  SimMapperCSMap m_smCS;

  using SimMapperFMap =
      llvm::DenseMap<const llvm::Function *, seadsa::SimulationMapper>;
  // simulation of BU graph vs SAS graph of the same Function
  SimMapperFMap m_smF;

  using NodesCSMap = llvm::DenseMap<const llvm::Instruction *, NodeSet>;
  NodesCSMap m_safen_cs_callee; // set of unsafe nodes in the callee of callsite
  NodesCSMap m_safen_cs_caller; // set of unsafe nodes in the caller of callsite

  using NodeFMap = llvm::DenseMap<const llvm::Function *, NodeSet>;
  NodeFMap m_safeSASF;
  NodeFMap m_safeBUF;

  using CellInfoMap =
      llvm::DenseMap<std::pair<const seadsa::Node *, unsigned>, CellInfo>;
  llvm::DenseMap<const llvm::Function *, CellInfoMap> m_fcim;
  llvm::DenseMap<const llvm::Instruction *, CellInfoMap> m_icim; // callsites

  expr::ExprFactory &m_efac;
  // -- constant base for keys
  expr::Expr m_keyBase;

public:
  InterMemPreProc(seadsa::CompleteCallGraph &ccg, seadsa::ShadowMem &shadowDsa,
                  expr::ExprFactory &efac);

  /*! \brief For each CallSite of a module, it obtains the simulation relation
   *   between the caller and the callee (context sensitive) and stores it.
   * This is used to compute which nodes are unsafe to copy.
   */
  bool runOnModule(llvm::Module &M);

  NodeSet &getSafeNodesCallerCS(const Instruction *I);
  NodeSet &getSafeNodesCalleeCS(const Instruction *I);

  unsigned getOffset(const Cell &c) {
    return m_shadowDsa.splitDsaNodes() ? c.getOffset() : 0;
  }

  bool isSafeNode(NodeSet &unsafe, const seadsa::Node *n);
  bool isSafeNode(const NodeSet &unsafe, const seadsa::Node *n);
  bool isSafeNodeFunc(const Node &n, const Function *f);

  void runOnFunction(const Function *f);

  seadsa::SimulationMapper &getSimulationF(const Function *f) {
    return m_smF[f];
  }

  seadsa::SimulationMapper &getSimulationCS(const CallSite &cs) {
    return m_smCS[cs.getInstruction()];
  }

  NodeSet &getSafeNodes(const Function *f) { return m_safeSASF[f]; }
  NodeSet &getSafeNodesBU(const Function *f) { return m_safeBUF[f]; }

  // \brief obtains the potential maximum number of cells encoded by `c` in `f`.
  // `c` must be in the SAS graph.
  unsigned getNumKeys(const Cell &c, const Function *f) {
    assert(m_fcim.count(f) > 0);
    if (m_fcim[f].count({c.getNode(), getOffset(c)}) == 0)
      return 0;
    else
      return m_fcim[f][{c.getNode(), getOffset(c)}].m_nks;
  }

  // \brief obtains the potential maximum number pointers that alias in `c` in
  // `f`. `c` must be in the SAS graph.
  unsigned getMaxAlias(const Cell &c, const Function *f) {
    return getMaxAlias(c.getNode(), getOffset(c), f);
  }
  // \brief same as `getMaxAlias(const Cell &c, const Function *f)`
  unsigned getMaxAlias(const Node *n, unsigned offset, const Function *f) {
    assert(m_fcim.count(f) > 0);
    if (m_fcim[f].count({n, offset}) == 0)
      return 0;
    else
      return m_fcim[f][{n, offset}].m_nacss;
  }

  unsigned getCINumKeysSummary(const Cell &c, const Function *f);
  unsigned getCIMaxAliasSummary(const Cell &c, const Function *f);

  expr::ExprVector &getKeysCell(const Cell &c, const Function *f);
  expr::ExprVector &getKeysCellSummary(const Cell &c, const Function *f);
  expr::ExprVector &getKeysCellCS(const Cell &cCallee, const Instruction *i);

  void precomputeFiniteMapTypes(const CallSite &CS, const NodeSet &safeBU,
                                const NodeSet &safeSAS);

  inline std::pair<const Node *, unsigned> cellToPair(const Cell &c) {
    return std::make_pair(c.getNode(), getOffset(c));
  }
  expr::Expr constraintsMemFunction(const Function *f, const FunctionInfo &fi,
                                    const CellExprMap &min,
                                    const CellExprMap &mout,
                                    LegacyOperationalSemantics &sem,
                                    SymStore &s);

private:
  void recProcessNode(const Cell &cFrom, const NodeSet &fromSafeNodes,
                      const NodeSet &toSafeNodes, SimulationMapper &smCS,
                      SimulationMapper &smCI, CellInfoMap &cim);
  template <typename ValueT>
  ValueT &findCellMap(DenseMap<std::pair<const Node *, unsigned>, ValueT> &map,
                      const Cell &c);
  expr::ExprVector &findKeysCellMap(CellKeysMap &map, const Cell &c);

  // !brief collects the keys that are modified per cell in `ckm`
  void recCollectAPsFunction(const Cell &cBU, const NodeSet &safeBU,
                             const NodeSet &safeSAS, const CellExprMap &mout,
                             SimulationMapper &sm, const Function *f,
                             Expr basePtr, CellKeysMap &ckm);

  // TODO: copied from UfoOpSem, merge
  bool hasExprCell(const CellExprMap &nim, const Cell &c);
  Expr getExprCell(const CellExprMap &nim, const Cell &c);
  Expr getExprCell(const CellExprMap &nim, const Node *n, unsigned offset);
};
} // namespace seahorn
