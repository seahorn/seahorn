#include "llvm/ADT/SCCIterator.h"

#include "seahorn/InterMemPreProc.hh"
#include "seahorn/Support/SeaDebug.h"

#include "sea_dsa/DsaAnalysis.hh"
#include "sea_dsa/CallGraphUtils.hh"
#include "sea_dsa/Global.hh"

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

using namespace llvm;

namespace seahorn {
// -- computes the safe nodes per callsite of a module
bool InterMemPreProc::runOnModule(Module &M) {

  const GlobalAnalysis &ga = m_shadowDsa.getDsaAnalysis();

  llvm::CallGraph &cg = m_ccg.getCompleteCallGraph();
  for (auto it = scc_begin(&cg); !it.isAtEnd(); ++it) {
    auto &scc = *it;
    for (CallGraphNode *cgn : scc) {
      Function *f_caller = cgn->getFunction();
      if (!f_caller || f_caller->isDeclaration() || f_caller->empty() || !ga.hasGraph(*f_caller))
        continue;

      for (auto &callRecord : *cgn) {
        llvm::Optional<DsaCallSite> dsaCS = call_graph_utils::getDsaCallSite(callRecord);
        if (!dsaCS.hasValue())
          continue;
        DsaCallSite &cs = dsaCS.getValue();
        const Function * f_callee = cs.getCallee();
        if (!ga.hasSummaryGraph(*f_callee))
          continue;

        LOG("inter_mem", errs() << "Preprocessing " << f_caller->getGlobalIdentifier(););

        ColorMap color_callee, color_caller;
        NodeSet f_node_safe;

        const Graph &callerG = ga.getGraph(*f_caller);
        const Graph &calleeG = ga.getSummaryGraph(*f_callee);

        std::unique_ptr<SimulationMapper> simMap = llvm::make_unique<SimulationMapper>();

        Graph::computeCalleeCallerMapping(cs, *(const_cast<Graph *>(&calleeG)),
                                          *(const_cast<Graph *>(&callerG)),
                                          *simMap);

        std::unique_ptr<NodeSet> unsafe_callee = llvm::make_unique<NodeSet>();
        std::unique_ptr<NodeSet> unsafe_caller = llvm::make_unique<NodeSet>();

        mark_nodes_graph(*(const_cast<Graph *>(&calleeG)), *f_callee,
                         *unsafe_callee, *unsafe_caller, *simMap);

        if(m_unsafen_f_callee.find(f_callee) == m_unsafen_f_callee.end()){
          std::unique_ptr<NodeSet> ci_unsafe = llvm::make_unique<NodeSet>();
          m_unsafen_f_callee[f_callee] = std::move(ci_unsafe);
        }
        NodeSet &ci_unsafe_callee = *m_unsafen_f_callee[f_callee];

        for (auto n : *unsafe_callee)
          if (!ci_unsafe_callee.count(n))
            ci_unsafe_callee.insert(n);

        const Instruction * I = cs.getInstruction();
        m_sms[I] = std::move(simMap);
        m_unsafen_cs_callee[I] = std::move(unsafe_callee);
        m_unsafen_cs_caller[I] = std::move(unsafe_caller);
      }
    }
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

