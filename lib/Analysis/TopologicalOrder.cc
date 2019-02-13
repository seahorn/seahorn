#include "seahorn/Analysis/TopologicalOrder.hh"

#include "seahorn/Support/SortTopo.hh"
#include "llvm/Analysis/CFG.h"

#include "boost/range/algorithm/binary_search.hpp"
#include "boost/range/algorithm/reverse.hpp"
#include "boost/range/algorithm/sort.hpp"


namespace seahorn {
char TopologicalOrder::ID = 0;

void TopologicalOrder::getAnalysisUsage(AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

bool TopologicalOrder::runOnFunction(Function &F) {
  m_backEdges.clear();
  m_order.clear();

  FindFunctionBackedges(F, m_backEdges);
  boost::sort(m_backEdges);

  RevTopoSort(F, m_order);
  boost::reverse(m_order);

  return false;
}

bool TopologicalOrder::isBackEdge(const BasicBlock &src,
                                  const BasicBlock &dst) const {
  return boost::binary_search(m_backEdges, std::make_pair(&src, &dst));
}

void TopologicalOrder::print(raw_ostream &out, const Module *m) const {
  out << "TOPO BEGIN\n";

  for (auto bb : *this)
    out << bb->getName() << " ";
  out << "\n";

  out << "TOPO END\n";
}

} // namespace seahorn

static llvm::RegisterPass<seahorn::TopologicalOrder>
    X("topo", "Topological order of CFG", true, true);
