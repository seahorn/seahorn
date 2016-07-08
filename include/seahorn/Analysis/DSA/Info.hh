#ifndef __DSA_INFO_HH_
#define __DSA_INFO_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/ADT/DenseMap.h"

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
       Graph* m_g;
       
       typedef std::vector<NodeInfo> NodeInfoVector;
       llvm::DenseMap<const Node*, NodeInfo> m_nodes_map;
       
       void addMemoryAccess (const llvm::Value* v); 
       void countMemoryAccesses (llvm::Module& M);

       void printMemoryAccesses (NodeInfoVector& v, llvm::raw_ostream&);
       void printMemoryTypes (NodeInfoVector& v, llvm::raw_ostream&);
       void printMemoryAllocSites (NodeInfoVector& v, llvm::raw_ostream&);
       
      public:
       
       static char ID;       
       
       Info () : ModulePass (ID), m_dl(nullptr), m_tli(nullptr), m_g(nullptr) {}

       void getAnalysisUsage (llvm::AnalysisUsage &AU) const override;

       bool runOnModule (llvm::Module &M) override;

       const char * getPassName() const { return "Dsa info pass"; }
    };
  }
}
#endif 
