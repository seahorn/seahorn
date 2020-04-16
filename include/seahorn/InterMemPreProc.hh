#pragma once

#include "seadsa/CompleteCallGraph.hh"
#include "seadsa/Mapper.hh"
#include "seadsa/ShadowMem.hh"
#include "seadsa/DsaColor.hh"

namespace seahorn {

  // preprocesor for vcgen with memory copies
  class InterMemPreProc {
    /*! \brief Keeps for each CallSite of a module the simulation relation
     * between the caller and the callee (context sensitive), the nodes that
     * unsafe to copy per callee, caller and function (context insensitive).
     */

  private:
    seadsa::CompleteCallGraph &m_ccg;
    seadsa::ShadowMem &m_shadowDsa;

    using SimMapperMap =
        llvm::DenseMap<const llvm::Instruction *,
                       std::unique_ptr<seadsa::SimulationMapper>>;
    SimMapperMap m_sms;

    using NodesCSMap = llvm::DenseMap<const llvm::Instruction *,
                                      std::unique_ptr<NodeSet>>;

    NodesCSMap
        m_unsafen_cs_callee; // set of unsafe nodes in the callee of callsite
    NodesCSMap
        m_unsafen_cs_caller; // set of unsafe nodes in the caller of callsite

    using NodeFMap = llvm::DenseMap<const llvm::Function *, std::unique_ptr<NodeSet>>;

    NodeFMap
        m_unsafen_f_callee; // set of unsafe nodes in the callee of a function

  public:
    InterMemPreProc(seadsa::CompleteCallGraph &ccg,
                    seadsa::ShadowMem &shadowDsa)
        : m_ccg(ccg), m_shadowDsa(shadowDsa){};

    /*! \brief For each CallSite of a module, it obtains the simulation relation
     *   between the caller and the callee (context sensitive) and stores it.
     * This is used to compute which nodes are unsafe to copy.
     */
    bool runOnModule(llvm::Module &M);
    NodeSet &getUnsafeCallerNodesCallSite(const llvm::CallSite &cs);
    bool isSafeNode(NodeSet &unsafe, const seadsa::Node *n);
    seadsa::SimulationMapper &getSimulationCallSite(const llvm::CallSite &cs);
  };
} // namespace seahorn
