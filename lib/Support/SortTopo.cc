#include "seahorn/Support/SortTopo.hh"
#include "llvm/ADT/Optional.h"
#include "llvm/Analysis/CFG.h"
#include "llvm/Support/raw_ostream.h"

namespace llvm {
class BlockedEdges {
  llvm::SmallPtrSet<const BasicBlock *, 8> m_set;
  llvm::SmallVectorImpl<std::pair<const BasicBlock *, const BasicBlock *>>
      &m_edges;

public:
  explicit BlockedEdges(
      llvm::SmallVectorImpl<std::pair<const BasicBlock *, const BasicBlock *>>
          &edges)
      : m_edges(edges) {
    std::sort(m_edges.begin(), m_edges.end());
  }

  bool insert(const BasicBlock *bb) { return m_set.insert(bb).second; }

  bool isBlockedEdge(const BasicBlock *src, const BasicBlock *dst) {
    return std::binary_search(m_edges.begin(), m_edges.end(),
                              std::make_pair(src, dst));
  }
};

template <> class po_iterator_storage<BlockedEdges, true> {
  BlockedEdges &Visited;

public:
  explicit po_iterator_storage(BlockedEdges &VSet) : Visited(VSet) {}
  po_iterator_storage(const po_iterator_storage &S) = default;

  bool insertEdge(Optional<const BasicBlock *> src, const BasicBlock *dst) {
    if (!src)
      return Visited.insert(dst);

    if (!Visited.isBlockedEdge(*src, dst))
      return Visited.insert(dst);

    return false;
  }
  void finishPostorder(const BasicBlock *bb) {}
};

} // namespace llvm

namespace seahorn {

void RevTopoSort(const llvm::Function &F,
                 std::vector<const BasicBlock *> &out) {
  if (F.isDeclaration() || F.empty())
    return;

  llvm::SmallVector<std::pair<const BasicBlock *, const BasicBlock *>, 8>
      backEdges;
  FindFunctionBackedges(F, backEdges);

  const llvm::Function *f = &F;
  BlockedEdges ble(backEdges);
  std::copy(po_ext_begin(f, ble), po_ext_end(f, ble), std::back_inserter(out));
}

} // namespace seahorn
