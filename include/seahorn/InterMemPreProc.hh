#pragma once

#include "sea_dsa/CompleteCallGraph.hh"
#include "sea_dsa/DsaColor.hh"
#include "sea_dsa/Mapper.hh"
#include "sea_dsa/ShadowMem.hh"

namespace seahorn {

// preprocesor for vcgen with memory copies
class InterMemPreProc {
  /*! \brief Keeps for each CallSite of a module the simulation relation between
   *   the caller and the callee (context sensitive), the nodes that unsafe to
   *   copy per callee, caller and function (context insensitive).
   */

private:
  CompleteCallGraph & m_ccg;
  ShadowMem & m_shadowDsa;

  using SimMapperMap =
      DenseMap<const Instruction *, std::unique_ptr<SimulationMapper>>;
  SimMapperMap m_sms;

  using NodesCSMap = DenseMap<const Instruction *, std::unique_ptr<NodeSet>>;

  NodesCSMap m_unsafen_cs_callee; // set of unsafe nodes in the callee of callsite
  NodesCSMap m_unsafen_cs_caller; // set of unsafe nodes in the caller of callsite

  using NodeFMap = DenseMap<const Function *, std::unique_ptr<NodeSet>>;

  NodeFMap m_unsafen_f_callee; // set of unsafe nodes in the callee of a function

public:
  InterMemPreProc(CompleteCallGraph &ccg, ShadowMem &shadowDsa)
      : m_ccg(ccg), m_shadowDsa(shadowDsa){};

  /*! \brief For each CallSite of a module, it obtains the simulation relation
   *   between the caller and the callee (context sensitive) and stores it. This
   *   is used to compute which nodes are unsafe to copy.
   */
  bool runOnModule(Module &M) ;
  NodeSet &getUnsafeCallerNodesCallSite(const CallSite &cs);
  bool isSafeNode(NodeSet &unsafe, const Node *n);
  SimulationMapper &getSimulationCallSite(const CallSite &cs);

};
} // namespace seahorn
