#include "seahorn/InterMemPreProc.hh"

#include "seahorn/Support/SeaDebug.h"

// #include "seahorn/Support/Stats.hh" // TODO: generate stats here

namespace seahorn {
// -- computes the safe nodes per callsite of a module
bool InterMemPreProc::runOnModule(Module &M) {

  auto &dsaCallGraph = m_ccg->getCompleteCallGraph();
  CallGraphWrapper dsaCG(dsaCallGraph);

  dsaCG.buildDependencies(); // TODO: this is already done already in other passes


  for (auto &F : M) {
    if (!m_shadowDsa->hasDsaGraph(F))
      continue;

    // store the contex insensitive unsafe nodes
    std::unique_ptr<NodeSet> ci_unsafe_callee(new NodeSet());

    auto call_sites = dsaCG.getUses(F);
    LOG("inter_mem", errs() << "Preprocessing " << F.getGlobalIdentifier(););

    for (auto it = call_sites.begin(); it != call_sites.end(); it++) {

      ColorMap color_callee, color_caller;
      NodeSet f_node_safe;

      const Function *f_caller = it->getCallSite().getCaller();

      Graph &callerG = m_shadowDsa->getDsaGraph(*f_caller);
      Graph &calleeG = m_shadowDsa->getSummaryGraph(F);

      std::unique_ptr<SimulationMapper> simMap(new SimulationMapper());

      Graph::computeCalleeCallerMapping(*it, *(const_cast<Graph *>(&calleeG)),
                                        *(const_cast<Graph *>(&callerG)),
                                        *simMap);

      std::unique_ptr<NodeSet> unsafe_callee(new NodeSet());
      std::unique_ptr<NodeSet> unsafe_caller(new NodeSet());

      GraphExplorer::getUnsafeNodesCallSite(*it, calleeG, callerG, *simMap,
                                            *unsafe_callee, *unsafe_caller);

      for (auto n : *unsafe_callee)
        if (!ci_unsafe_callee->count(n))
          ci_unsafe_callee->insert(n);

      const Instruction *inst = it->getInstruction();

      m_sms[inst] = std::move(simMap);
      m_safen_cs_callee[inst] = std::move(unsafe_callee);
      m_safen_cs_caller[inst] = std::move(unsafe_caller);

    }
    m_safen_f_callee[&F] = std::move(ci_unsafe_callee);
    // TODO: also store ci caller
  }
  return false;
}

NodeSet & InterMemPreProc::getSafeCallerNodesCallSite(const CallSite cs){
  auto ns = m_safen_cs_caller.find(cs.getInstruction());
  assert(ns != m_safen_cs_caller.end());
  return *ns->getSecond();
}
SimulationMapper &InterMemPreProc::getSimulationCallSite(const CallSite cs) {
  auto ns = m_sms.find(cs.getInstruction());
  assert(ns != m_sms.end());

  return *ns->getSecond();
}

} // namespace seahorn
