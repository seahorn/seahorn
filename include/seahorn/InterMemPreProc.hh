#pragma once

#include "sea_dsa/ShadowMem.hh"

#include "sea_dsa/CompleteCallGraph.hh"
#include "sea_dsa/DsaColor.hh"

namespace seahorn {

// preprocesor for vcgen with memory copies
class InterMemPreProc {

private:
  CompleteCallGraph * m_ccg = nullptr;
  ShadowMem & m_shadowDsa;

  using SimMapperMap =
      DenseMap<const Instruction *, std::unique_ptr<SimulationMapper>>;
  SimMapperMap m_sms;

  using NodesCSMap = DenseMap<const Instruction *, std::unique_ptr<NodeSet>>;

  NodesCSMap m_safen_cs_callee; // set of unsafe nodes in the callee of callsite
  NodesCSMap m_safen_cs_caller; // set of unsafe nodes in the caller of callsite

  using NodeFMap = DenseMap<const Function *, std::unique_ptr<NodeSet>>;

  NodeFMap m_safen_f_callee; // set of unsafe nodes in the callee of a function

public:
  InterMemPreProc(CompleteCallGraph *ccg, ShadowMem &shadowDsa)
      : m_ccg(ccg), m_shadowDsa(shadowDsa){};

  bool runOnModule(Module &M) ;
  NodeSet &getSafeCallerNodesCallSite(CallSite cs);
  SimulationMapper &getSimulationCallSite(CallSite cs);

};
} // namespace seahorn
