#pragma once

/**
   Extra utilities for Boost Graph Library
 */
#include "boost/graph/graph_traits.hpp"
#include "boost/property_map/property_map.hpp"
#include "boost/typeof/typeof.hpp"

#include "seahorn/Support/PropertyMapExtras.hh"

/** Useful functions over BGL graphs */

namespace seahorn {
template <typename Graph, typename BoolVertexMap>
void slice(const Graph &g, typename graph_traits<Graph>::vertex_descriptor en,
           typename graph_traits<Graph>::vertex_descriptor ex,
           BoolVertexMap out) {
  NodeSet reachExit;
  BOOST_AUTO(reachExitPM, make_set_property_map(reachExit));
  reaches(g, ex, reachExitPM);

  // -- en does not reach ex
  if (reachExit.count(en) <= 0)
    return;

  BOOST_AUTO(edgPred, make_vertex_edge_predicate(g, reachExitPM));
  reachable(make_filtered_graph(g, edgPred), en, out);
}

template <typename Graph, typename BoolVertexMap>
void reaches(const Graph &g, typename graph_traits<Graph>::vertex_descriptor n,
             BoolVertexMap out) {
  typedef typename graph_traits<Graph>::edge_descriptor Edge;

  if (get(out, n))
    return;
  put(out, n, true);
  forall(Edge edg, in_edges(n, g)) reaches(g, source(edg, g), out);
}

template <typename Graph, typename BoolVertexMap>
void reachable(const Graph &g,
               typename graph_traits<Graph>::vertex_descriptor n,
               BoolVertexMap out) {
  typedef typename graph_traits<Graph>::edge_descriptor Edge;
  if (get(out, n))
    return;

  put(out, n, true);
  foreach (Edge edg, out_edges(n, g))
    reachable(g, target(edg, g), out);
}

/**
 * Returns true if v is a root of graph g
 *
 * \tparam Graph BGL graph
 * \param[in] v vertex
 * \param[in] g graph
 *
 * \return true if v is root of g
 */
template <typename Graph>
bool isRoot(typename graph_traits<Graph>::vertex_descriptor v, const Graph &g) {
  return in_degree(v, g) == 0;
}

/**
 * Returns true if v is a leaf of graph g
 *
 * \tparam Graph BGL graph
 * \param[in] v vertex
 * \param[in] g graph
 *
 * \return true if v is root of g
 */
template <typename Graph>
bool isLeaf(typename graph_traits<Graph>::vertex_descriptor v, const Graph &g) {
  return out_degree(v, g) == 0;
}

} // namespace seahorn
