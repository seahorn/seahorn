#ifndef _HCDB_BOOST_GRAPH_TRAITS_HPP__
#define _HCDB_BOOST_GRAPH_TRAITS_HPP__

/* View of a HornClauseDB as a BGL graph */

#include "seahorn/HornClauseDB.hh"
#include "seahorn/Expr/Expr.hh"

#include <boost/iterator/transform_iterator.hpp>
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/properties.hpp>

namespace seahorn
{
  namespace bgl
  {
    typedef std::pair<expr::Expr, expr::Expr> EEPair; // fdecl -> fdecl

    struct MkOutEdgePair : public std::unary_function<expr::Expr, EEPair>
    {
      expr::Expr src; 
      MkOutEdgePair () : src (NULL) {}
      MkOutEdgePair (expr::Expr u) : src (u) 
      { assert (expr::op::bind::isFdecl(u)); }

      EEPair operator() (expr::Expr dst) const
      { 
        assert (src);
        assert (expr::op::bind::isFdecl(dst));
        return std::make_pair (src, dst); 
      }
    };

    struct MkInEdgePair : public std::unary_function<expr::Expr,EEPair>
    {
      expr::Expr dst;
    
      MkInEdgePair () : dst(NULL) {}    
      MkInEdgePair (expr::Expr v) : dst(v) 
      { assert (expr::op::bind::isFdecl(dst)); }
      EEPair operator() (expr::Expr src) const 
      { 
        assert (dst); 
        assert (expr::op::bind::isFdecl(src));
        return std::make_pair (src, dst); 
      }
    };  
    
  }
}


namespace boost
{
  template<> 
  struct graph_traits<seahorn::HornClauseDBCallGraph>
  {
    typedef expr::Expr vertex_descriptor; // fdecl
    typedef seahorn::bgl::EEPair edge_descriptor;
    
    typedef disallow_parallel_edge_tag edge_parallel_category;
    typedef bidirectional_tag directed_category;
    struct this_graph_tag : 
      virtual bidirectional_graph_tag, virtual vertex_list_graph_tag {};
    typedef this_graph_tag traversal_category;
    
    typedef size_t vertices_size_type;
    typedef size_t edges_size_type;
    typedef size_t degree_size_type;

    typedef boost::transform_iterator<seahorn::bgl::MkOutEdgePair, 
                                      seahorn::HornClauseDB::expr_set_type::const_iterator> 
    out_edge_iterator;
    
    typedef boost::transform_iterator<seahorn::bgl::MkInEdgePair, 
                                      seahorn::HornClauseDB::expr_set_type::const_iterator>
    in_edge_iterator;

    typedef seahorn::HornClauseDB::expr_set_type::const_iterator vertex_iterator;

    /** unimplemented iterator over edges to make filtered_graph happy */
    typedef in_edge_iterator edge_iterator;

    static vertex_descriptor null_vertex () { return NULL; }    
  };
  
  inline expr::Expr source (const seahorn::bgl::EEPair e, const seahorn::HornClauseDBCallGraph &callgraph)
  { return e.first; }

  inline expr::Expr target (const seahorn::bgl::EEPair e, const seahorn::HornClauseDBCallGraph &callgraph)
  { return e.second; }


  namespace
  {
    typedef typename graph_traits<seahorn::HornClauseDBCallGraph>::out_edge_iterator out_eit;
    typedef typename graph_traits<seahorn::HornClauseDBCallGraph>::in_edge_iterator in_eit;
    typedef typename graph_traits<seahorn::HornClauseDBCallGraph>::vertex_iterator vit;
  }
    
  inline std::pair<out_eit,out_eit> out_edges (expr::Expr e, const seahorn::HornClauseDBCallGraph &callgraph)
  {
    auto const &callees = callgraph.callees(e);
    return std::make_pair
        (make_transform_iterator (callees.begin(), seahorn::bgl::MkOutEdgePair (e)),
         make_transform_iterator (callees.end(), seahorn::bgl::MkOutEdgePair (e)));
  }
  
  inline size_t out_degree (expr::Expr e, const seahorn::HornClauseDBCallGraph &callgraph)
  { return callgraph.callees(e).size(); }

  inline std::pair<in_eit, in_eit> in_edges (expr::Expr e, const seahorn::HornClauseDBCallGraph &callgraph)
  {
    auto const &callers = callgraph.callers(e);
    return std::make_pair
        (make_transform_iterator (callers.begin(), seahorn::bgl::MkInEdgePair (e)),
         make_transform_iterator (callers.end(), seahorn::bgl::MkInEdgePair (e)));
  }
  
  inline size_t in_degree (expr::Expr e, const seahorn::HornClauseDBCallGraph &callgraph)
  { return callgraph.callers(e).size(); }
  
  inline size_t degree (expr::Expr e, const seahorn::HornClauseDBCallGraph &callgraph)
  { return callgraph.callees(e).size() + callgraph.callers(e).size(); }
  
  inline std::pair<vit,vit> vertices (const seahorn::HornClauseDBCallGraph &callgraph)
  { return std::make_pair (callgraph.m_db.getRelations().begin(), callgraph.m_db.getRelations().end()); }
  
  inline size_t num_vertices (const seahorn::HornClauseDBCallGraph &callgraph)
  { return callgraph.m_db.getRelations().size(); }

}
#endif  /*  _HCDB_BOOST_GRAPH_TRAITS_HPP__ */
