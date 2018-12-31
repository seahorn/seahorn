#ifndef __LLVM_BGL_HPP_
#define __LLVM_BGL_HPP_
/** BGL interface to LLVM CFG */

#include "llvm/IR/CFG.h"

#include <boost/graph/graph_traits.hpp>
#include <boost/graph/properties.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/property_map/property_map.hpp>

namespace llvm {
typedef std::pair<BasicBlock *, BasicBlock *> BBPair;
namespace bgl {
struct MkOutEdgePair : public std::unary_function<BasicBlock *, BBPair> {
  BasicBlock *src;
  MkOutEdgePair() : src(NULL) {}
  MkOutEdgePair(BasicBlock *u) : src(u) {}

  BBPair operator()(BasicBlock *v) const {
    assert(src);
    return std::make_pair(src, v);
  }
};

struct MkInEdgePair : public std::unary_function<BasicBlock *, BBPair> {
  BasicBlock *dst;

  MkInEdgePair() : dst(NULL) {}

  MkInEdgePair(BasicBlock *v) : dst(v) {}
  BBPair operator()(BasicBlock *u) const {
    assert(dst);
    return std::make_pair(u, dst);
  }
};

} // namespace bgl
} // namespace llvm

namespace boost {
template <> struct graph_traits<llvm::Function> {
  typedef llvm::BasicBlock *vertex_descriptor;
  typedef llvm::BBPair edge_descriptor;

  typedef disallow_parallel_edge_tag edge_parallel_category;
  typedef bidirectional_tag directed_category;
  struct this_graph_tag : virtual bidirectional_graph_tag,
                          virtual vertex_list_graph_tag {};
  typedef this_graph_tag traversal_category;

  typedef size_t vertices_size_type;
  typedef size_t edges_size_type;
  typedef size_t degree_size_type;

  typedef boost::transform_iterator<llvm::bgl::MkOutEdgePair,
                                    llvm::succ_iterator>
      out_edge_iterator;

  typedef boost::transform_iterator<llvm::bgl::MkInEdgePair,
                                    llvm::pred_iterator>
      in_edge_iterator;

  typedef llvm::Function::const_iterator vertex_iterator;

  /** unimplemented iterator over edges to make filtered_graph happy */
  typedef in_edge_iterator edge_iterator;

  static vertex_descriptor null_vertex() { return NULL; }
};

inline llvm::BasicBlock *source(const llvm::BBPair e, const llvm::Function &f) {
  return e.first;
}

inline llvm::BasicBlock *target(const llvm::BBPair e, const llvm::Function &f) {
  return e.second;
}
} // namespace boost

namespace llvm {
namespace bgl {
typedef
    typename boost::graph_traits<::llvm::Function>::out_edge_iterator out_eit;
typedef typename boost::graph_traits<::llvm::Function>::in_edge_iterator in_eit;
typedef llvm::Function::const_iterator vit;
} // namespace bgl
} // namespace llvm

namespace boost {
inline std::pair<llvm::bgl::out_eit, llvm::bgl::out_eit>
out_edges(llvm::BasicBlock *bb, const llvm::Function &f) {
  return std::make_pair(
      make_transform_iterator(succ_begin(bb), llvm::bgl::MkOutEdgePair(bb)),
      make_transform_iterator(succ_end(bb), llvm::bgl::MkOutEdgePair(bb)));
}

inline size_t out_degree(const llvm::BasicBlock *bb, const llvm::Function &f) {
  return bb->getTerminator()->getNumSuccessors();
}

inline std::pair<llvm::bgl::in_eit, llvm::bgl::in_eit>
in_edges(llvm::BasicBlock *bb, const llvm::Function &f) {
  return std::make_pair(
      make_transform_iterator(pred_begin(bb), llvm::bgl::MkInEdgePair(bb)),
      make_transform_iterator(pred_end(bb), llvm::bgl::MkInEdgePair(bb)));
}

inline size_t in_degree(const llvm::BasicBlock *bb, const llvm::Function &f) {
  return bb->getNumUses();
}

inline size_t degree(const llvm::BasicBlock *bb, const llvm::Function &f) {
  return bb->getNumUses() + bb->getTerminator()->getNumSuccessors();
}

inline std::pair<llvm::bgl::vit, llvm::bgl::vit>
vertices(const llvm::Function &f) {
  return std::make_pair(f.begin(), f.end());
}

inline size_t num_vertices(const llvm::Function &f) { return f.size(); }

} // namespace boost

#endif
