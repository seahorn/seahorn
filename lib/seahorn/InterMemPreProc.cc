#include "seahorn/InterMemPreProc.hh"

#include "sea_dsa/CallGraphWrapper.hh"
#include "sea_dsa/Global.hh"

#include "seahorn/Support/SeaDebug.h"


namespace {

using namespace sea_dsa;

enum class EColor { BLACK, GRAY }; // colors for exploration
using ExplorationMap = DenseMap<const Node *, EColor>;

bool isSafeNode(NodeSet &unsafe, const Node *n) { return unsafe.count(n) == 0; }

void propagate_not_copy(const Node &n, ExplorationMap &f_color, NodeSet &f_safe,
                        NodeSet &f_safe_caller, SimulationMapper &sm) {
  if (isSafeNode(f_safe, &n))
    f_safe.insert(&n); // we store the ones that are not safe

  f_color[&n] = EColor::BLACK;

  for (auto &links : n.getLinks()) {
    const Field &f = links.first;
    const Cell &next_c = *links.second;
    const Node *next_n = next_c.getNode();

    auto next = f_color.find(next_n);

    bool explored = next != f_color.end() && next->getSecond() == EColor::BLACK;
    bool marked_safe = isSafeNode(f_safe, next_n);

    if (!(explored && !marked_safe)) {
      const Node &next_n_caller = *sm.get(next_c).getNode();

      if (isSafeNode(f_safe_caller, &next_n_caller))
        f_safe_caller.insert(&next_n_caller);

      propagate_not_copy(*next_n, f_color, f_safe, f_safe_caller, sm);
    }
  }
}

bool mark_copy(const Node &n, ExplorationMap &f_color, NodeSet &f_safe,
               NodeSet &f_safe_caller, SimulationMapper &sm) {
  f_color[&n] = EColor::GRAY;

  for (auto &links : n.getLinks()) {
    const Field &f = links.first;
    const Cell &next_c = *links.second;
    const Node *next_n = next_c.getNode();
    auto it = f_color.find(next_n);
    if (next_n->isArray()){ // encodes an object of unbounded size
      propagate_not_copy(n, f_color, f_safe, f_safe_caller, sm);
      return true;
    }
    else if (it == f_color.end() && mark_copy(*next_n, f_color, f_safe,f_safe_caller,sm)) {
      return true;
    } else if (it != f_color.end() && it->getSecond() == EColor::GRAY) {
      propagate_not_copy(n, f_color, f_safe,f_safe_caller,sm);
      return true;
    }
  }

  f_color[&n] = EColor::BLACK;

  return false;
}

void mark_nodes_graph(Graph &g, const Function &F, NodeSet &f_safe,
                      NodeSet &f_safe_caller, SimulationMapper &sm) {
  ExplorationMap f_visited;

  for (const Argument &a : F.args()) {
    if (g.hasCell(a)) { // scalar arguments don't have cells
      const Cell &c = g.getCell(a);
      const Node *n = c.getNode();
      mark_copy(*n, f_visited, f_safe, f_safe_caller, sm);
    }
  }
}

} // namespace


namespace seahorn {
// -- computes the safe nodes per callsite of a module
bool InterMemPreProc::runOnModule(Module &M) {

  auto &dsaCallGraph = m_ccg.getCompleteCallGraph();
  CallGraphWrapper dsaCG(dsaCallGraph);

  dsaCG.buildDependencies(); // TODO: this is already done already in other passes
  const GlobalAnalysis &ga = m_shadowDsa.getDsaAnalysis();

  for (auto &F : M) {
    if (!ga.hasGraph(F))
      continue;

    // store the context-insensitive unsafe nodes
    std::unique_ptr<NodeSet> ci_unsafe_callee = llvm::make_unique<NodeSet>();

    auto call_sites = dsaCG.getUses(F);
    LOG("inter_mem", errs() << "Preprocessing " << F.getGlobalIdentifier(););

    for (auto it = call_sites.begin(); it != call_sites.end(); it++) {

      ColorMap color_callee, color_caller;
      NodeSet f_node_safe;

      const Function *f_caller = it->getCallSite().getCaller();

      const Graph &callerG = ga.getGraph(*f_caller);
      const Graph &calleeG = ga.getSummaryGraph(F);

      std::unique_ptr<SimulationMapper> simMap =
          llvm::make_unique<SimulationMapper>();

      Graph::computeCalleeCallerMapping(*it, *(const_cast<Graph *>(&calleeG)),
                                        *(const_cast<Graph *>(&callerG)),
                                        *simMap);

      std::unique_ptr<NodeSet> unsafe_callee = llvm::make_unique<NodeSet>();
      std::unique_ptr<NodeSet> unsafe_caller = llvm::make_unique<NodeSet>();

      mark_nodes_graph(*(const_cast<Graph *>(&calleeG)), *it->getCallee(),
                       *unsafe_callee, *unsafe_caller, *simMap);

      for (auto n : *unsafe_callee)
        if (!ci_unsafe_callee->count(n))
          ci_unsafe_callee->insert(n);

      const Instruction *inst = it->getInstruction();

      m_sms[inst] = std::move(simMap);
      m_unsafen_cs_callee[inst] = std::move(unsafe_callee);
      m_unsafen_cs_caller[inst] = std::move(unsafe_caller);

    }
    m_unsafen_f_callee[&F] = std::move(ci_unsafe_callee);
  }
  return false;
}

NodeSet &InterMemPreProc::getUnsafeCallerNodesCallSite(const CallSite &cs) {
  auto ns = m_unsafen_cs_caller.find(cs.getInstruction());
  assert(ns != m_unsafen_cs_caller.end());
  return *ns->getSecond();
}
SimulationMapper &InterMemPreProc::getSimulationCallSite(const CallSite &cs) {
  auto ns = m_sms.find(cs.getInstruction());
  assert(ns != m_sms.end());

  return *ns->getSecond();
}

bool InterMemPreProc::isSafeNode(NodeSet &unsafe, const Node *n) {
  return ::isSafeNode(unsafe, n);
}

} // namespace seahorn

