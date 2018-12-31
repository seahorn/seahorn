#pragma once
/// An adapter between llvm::GraphTraits and boost::graph_traits

#include "llvm/ADT/GraphTraits.h"

#include <boost/graph/graph_traits.hpp>
#include <boost/graph/properties.hpp>
#include <boost/iterator/transform_iterator.hpp>

namespace seahorn {

namespace graph {
template <typename T> struct llvm_null_trait {};

template <typename T> struct llvm_null_trait<T *> {
  static inline T *null_value() { return NULL; }
};

template <typename G>
struct MkOutEdge : public std::unary_function<
                       typename boost::graph_traits<G>::vertex_descriptor,
                       typename boost::graph_traits<G>::edge_descriptor> {
  typedef typename boost::graph_traits<G>::vertex_descriptor Node;
  typedef typename boost::graph_traits<G>::edge_descriptor Edge;

  Node m_src;

  MkOutEdge() {}
  MkOutEdge(Node &src) : m_src(src) {}

  Edge operator()(Node &dst) const { return Edge(m_src, dst); }
};

template <typename G>
struct MkInEdge : public std::unary_function<
                      typename boost::graph_traits<G>::vertex_descriptor,
                      typename boost::graph_traits<G>::edge_descriptor> {
  typedef typename boost::graph_traits<G>::vertex_descriptor Node;
  typedef typename boost::graph_traits<G>::edge_descriptor Edge;

  Node m_dst;

  MkInEdge() {}
  MkInEdge(Node &dst) : m_dst(dst) {}

  Edge operator()(Node &src) const { return Edge(src, m_dst); }
};
} // namespace graph

} // namespace seahorn

namespace boost {
template <typename Graph> struct graph_traits<Graph *> {
  typedef Graph *GraphPtr;
  typedef llvm::GraphTraits<GraphPtr> llvm_graph;
  typedef typename llvm_graph::ChildIteratorType llvm_succ_iterator;

  typedef llvm::GraphTraits<llvm::Inverse<GraphPtr>> llvm_inverse_graph;
  typedef typename llvm_inverse_graph::ChildIteratorType llvm_pred_iterator;

  typedef typename llvm_graph::NodeType *vertex_descriptor;
  typedef typename std::pair<vertex_descriptor, vertex_descriptor>
      edge_descriptor;

  typedef std::pair<const vertex_descriptor, const vertex_descriptor>
      const_edge_descriptor;

  typedef disallow_parallel_edge_tag edge_parallel_category;
  typedef bidirectional_tag directed_category;
  struct this_graph_tag : virtual bidirectional_graph_tag,
                          virtual vertex_list_graph_tag {};
  typedef this_graph_tag traversal_category;

  typedef size_t vertices_size_type;
  typedef size_t edges_size_type;
  typedef size_t degree_size_type;

  typedef boost::transform_iterator<seahorn::graph::MkOutEdge<GraphPtr>,
                                    llvm_succ_iterator>
      out_edge_iterator;

  typedef boost::transform_iterator<seahorn::graph::MkInEdge<GraphPtr>,
                                    llvm_pred_iterator>
      in_edge_iterator;

  typedef typename llvm_graph::nodes_iterator vertex_iterator;

  /** unimplemented iterator over edges to make filtered_graph happy */
  typedef in_edge_iterator edge_iterator;

  static vertex_descriptor null_vertex() {
    return seahorn::graph::llvm_null_trait<vertex_descriptor>::null_value();
  }
};

template <typename G>
typename graph_traits<G *>::vertex_descriptor
source(typename graph_traits<G *>::edge_descriptor e, G *g) {
  return e.first;
}

template <typename G>
typename graph_traits<G *>::vertex_descriptor
target(typename graph_traits<G *>::edge_descriptor e, G *g) {
  return e.second;
}

template <typename G>
std::pair<typename graph_traits<G *>::out_edge_iterator,
          typename graph_traits<G *>::out_edge_iterator>
out_edges(typename graph_traits<G *>::vertex_descriptor v, G *g) {
  return std::make_pair(
      make_transform_iterator(llvm::GraphTraits<G *>::child_begin(v),
                              seahorn::graph::MkOutEdge<G *>(v)),
      make_transform_iterator(llvm::GraphTraits<G *>::child_end(v),
                              seahorn::graph::MkOutEdge<G *>(v)));
}

template <typename G>
size_t out_degree(typename graph_traits<G *>::vertex_descriptor v, G *g) {
  return std::distance(llvm::GraphTraits<G *>::child_begin(v),
                       llvm::GraphTraits<G *>::child_end(v));
}

template <typename G>
std::pair<typename graph_traits<G *>::in_edge_iterator,
          typename graph_traits<G *>::in_edge_iterator>
in_edges(typename graph_traits<G *>::vertex_descriptor v, G *g) {
  return std::make_pair(
      make_transform_iterator(
          llvm::GraphTraits<llvm::Inverse<G *>>::child_begin(v),
          seahorn::graph::MkInEdge<G *>(v)),
      make_transform_iterator(
          llvm::GraphTraits<llvm::Inverse<G *>>::child_end(v),
          seahorn::graph::MkInEdge<G *>(v)));
}

template <typename G>
size_t in_degree(typename graph_traits<G *>::vertex_descriptor v, G *g) {
  return std::distance(llvm::GraphTraits<llvm::Inverse<G *>>::child_begin(v),
                       llvm::GraphTraits<llvm::Inverse<G *>>::child_end(v));
}

template <typename G>
size_t degree(typename graph_traits<G *>::vertex_descriptor v, G *g) {
  return out_degree(v, g) + in_degree(v, g);
}

template <typename G>
std::pair<typename graph_traits<G *>::vertex_iterator,
          typename graph_traits<G *>::vertex_iterator>
vertices(G *g) {
  return std::make_pair(llvm::GraphTraits<G *>::nodes_begin(g),
                        llvm::GraphTraits<G *>::nodes_end(g));
}

template <typename G> size_t num_vertices(G *g) {
  return std::distance(llvm::GraphTraits<G *>::nodes_begin(g),
                       llvm::GraphTraits<G *>::nodes_end(g));
}

} // namespace boost
