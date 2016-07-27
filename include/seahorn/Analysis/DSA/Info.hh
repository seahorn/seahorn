#ifndef __DSA_INFO_HH_
#define __DSA_INFO_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "boost/unordered_map.hpp"
#include <boost/iterator/transform_iterator.hpp>
#include <boost/range/iterator_range.hpp>
#include "boost/iterator/filter_iterator.hpp"

#include "seahorn/Analysis/DSA/Global.hh"

/* Gather information for dsa clients and compute some stats */

namespace llvm 
{
    class DataLayout;
    class TargetLibraryInfo;
    class Value;
    class raw_ostream;
}

namespace seahorn 
{
  namespace dsa 
  {
    class Node;
    class Graph;
  }
}


namespace seahorn 
{
  namespace dsa 
  {

    // Wrapper to extend a dsa node with extra information
    class NodeInfo {
      
      const Node* m_node; 
      unsigned m_id;
      unsigned m_accesses;
      
     public:
  
      NodeInfo (const Node* node, unsigned id)
          : m_node(node), m_id(id), m_accesses(0) {}
      
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

     class Info : public llvm::ModulePass
     {
       const llvm::DataLayout *m_dl;
       const llvm::TargetLibraryInfo *m_tli;
       DsaGlobalPass *m_dsa;

       typedef boost::unordered_map<const Node*, NodeInfo> NodeInfoMap;
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
       

       NodeInfoMap m_nodes_map;

       Graph* getGraph (const llvm::Function& f) const;

       void addMemoryAccess (const llvm::Value* v, Graph& g); 
       void countMemoryAccesses (llvm::Function& f);

       void printMemoryAccesses (live_nodes_const_range nodes, llvm::raw_ostream&o) const;
       void printMemoryTypes (live_nodes_const_range nodes, llvm::raw_ostream&o) const;
       void printMemoryAllocSites (live_nodes_const_range nodes, llvm::raw_ostream&o) const;


      public:
       
       static char ID;       
       
       Info () : ModulePass (ID), m_dl(nullptr), m_tli(nullptr), m_dsa(nullptr) {}

       void getAnalysisUsage (llvm::AnalysisUsage &AU) const override;

       bool runOnModule (llvm::Module &M) override;

       bool runOnFunction (llvm::Function &F) ;

       const char * getPassName() const { return "Dsa info pass"; }
    };
  }
}
#endif 
