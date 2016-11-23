#ifndef __DSA_INFO_HH_
#define __DSA_INFO_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "boost/container/flat_set.hpp"
#include <boost/unordered_map.hpp>
#include <boost/iterator/transform_iterator.hpp>
#include <boost/range/iterator_range.hpp>
#include <boost/iterator/filter_iterator.hpp>
#include <boost/bimap.hpp>

/* Gather information for dsa clients and compute some stats */

namespace llvm 
{
    class DataLayout;
    class TargetLibraryInfo;
    class Value;
    class Function;
    class raw_ostream;
}

namespace seahorn 
{
  namespace dsa 
  {
    class Node;
    class Graph; 
    class GlobalAnalysis;
  }
}


namespace seahorn 
{
  namespace dsa 
  {

    // Wrapper to extend a dsa node with extra information
    class NodeInfo 
    {      
      const Node* m_node; 
      unsigned m_id;
      unsigned m_accesses;
      // Name of one of the node's referrers.
      // The node is chosen deterministically 
      std::string m_rep_name;

     public:
  
      NodeInfo (const Node* node, unsigned id, std::string name)
          : m_node(node), m_id(id), m_accesses(0), m_rep_name (name) {}
      
      bool operator==(const NodeInfo&o) const 
      {  
         // XXX: we do not want to use pointer addresses here
         return (getId() == o.getId());
      }

      bool operator<(const NodeInfo&o) const 
      {   
         // XXX: we do not want to use pointer addresses here
         return (getId() < o.getId());
      }
      
      const Node* getNode () const { return m_node; }
      const unsigned getId () const { return m_id;}
      NodeInfo& operator++ () // prefix ++
      {
        m_accesses++;
        return *this;
      }

      unsigned getAccesses () const { return m_accesses;}
    };

    class InfoAnalysis
    {
      typedef boost::unordered_map<const Node*, NodeInfo> NodeInfoMap;
      typedef boost::bimap<const llvm::Value*, unsigned int> AllocSiteBiMap;
      typedef boost::container::flat_set<const llvm::Value*> ValueSet;
      typedef boost::container::flat_set<unsigned int> IdSet;
      typedef boost::container::flat_set<NodeInfo> NodeInfoSet;
      typedef boost::container::flat_set<Graph*> GraphSet;
      typedef boost::unordered_map<const llvm::Value*, std::string> NamingMap;

      const llvm::DataLayout &m_dl;
      const llvm::TargetLibraryInfo &m_tli;
      GlobalAnalysis &m_dsa;
      bool m_verbose;

      NodeInfoMap m_nodes_map; // map Node to NodeInfo
      AllocSiteBiMap m_alloc_sites; // bimap allocation sites to id
      NamingMap m_names; // map Value to string name

      GraphSet m_seen_graphs;
      typedef typename NodeInfoMap::value_type binding_t;
      
      struct get_second : public std::unary_function<binding_t, NodeInfo> 
      { const NodeInfo& operator()(const binding_t &kv) const { return kv.second;}};
      typedef boost::transform_iterator<get_second, typename NodeInfoMap::const_iterator> nodes_const_iterator;
      typedef boost::iterator_range<nodes_const_iterator> nodes_const_range;
      
      struct is_alive_node { bool operator()(const NodeInfo&);};
      typedef boost::filter_iterator<is_alive_node, nodes_const_iterator> live_nodes_const_iterator;
      typedef boost::iterator_range<live_nodes_const_iterator> live_nodes_const_range;
      
      nodes_const_iterator nodes_begin () const
      {
        return boost::make_transform_iterator(m_nodes_map.begin(), get_second());
      }
      
      nodes_const_iterator nodes_end () const
      {
        return boost::make_transform_iterator(m_nodes_map.end(), get_second());
      }
      
      nodes_const_range nodes () const
      {
        return boost::make_iterator_range(nodes_begin (), nodes_end());
      }
      
      live_nodes_const_iterator live_nodes_begin () const
      {
        return boost::make_filter_iterator (is_alive_node(), nodes_begin());
      }
      
      live_nodes_const_iterator live_nodes_end () const
      {
         return boost::make_filter_iterator (is_alive_node(), nodes_end());
      }
      
      live_nodes_const_range live_nodes () const
      {
        return boost::make_iterator_range (live_nodes_begin (), live_nodes_end());
      }

      std::string getName (const llvm::Function &fn, const llvm::Value& v);       

      void addMemoryAccess (const llvm::Value* v, Graph& g, const llvm::Instruction &I); 

      void countMemoryAccesses (const llvm::Function& f);

      void assignNodeId (const llvm::Function &fn, Graph* g);

      void assignAllocSiteIdAndPrinting (live_nodes_const_range nodes, llvm::raw_ostream&o,
                                         std::string outFile);

      void printMemoryAccesses (live_nodes_const_range nodes, llvm::raw_ostream&o) const;

      void printMemoryTypes (live_nodes_const_range nodes, llvm::raw_ostream&o) const;
      
      public:
       
      InfoAnalysis (const llvm::DataLayout &dl, const llvm::TargetLibraryInfo &tli,
                    GlobalAnalysis &dsa, bool verbose = true)
          : m_dl (dl), m_tli (tli), m_dsa (dsa), m_verbose (verbose) {}

      bool runOnModule (llvm::Module &M);
      bool runOnFunction (llvm::Function &fn);

      /// API for Dsa clients

      Graph* getDsaGraph (const llvm::Function& f) const;

      bool isAccessed (const Node&n) const; 

      // return unique numeric identifier for node n if found,
      // otherwise 0
      unsigned int getDsaNodeId (const Node&n) const;

      // return unique numeric identifier for Value if it is an
      // allocation site, otherwise 0.
      unsigned int getAllocSiteId (const llvm::Value* V) const;

      // the inverse of getAllocSiteID
      const llvm::Value* getAllocValue (unsigned int alloc_site_id) const;

    };

  }
}
#endif 
