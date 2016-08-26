#ifndef __DSA__CLONER__HH_
#define __DSA__CLONER__HH_
#include "seahorn/Analysis/DSA/Graph.hh"

namespace seahorn
{
  namespace dsa
  {
    /** 
     * Recursively clone DSA sub-graph rooted at a given Node
     */
    class Cloner
    {
      Graph &m_graph;
      llvm::DenseMap<const Node*, Node*> m_map;
      
    public:
      Cloner (Graph &g) : m_graph(g) {}
      
      /// Returns a clone of a given node in the new graph
      /// Recursive clones nodes linked by this node as necessary
      Node &clone (const Node &n);

      /// Returns a cloned node that corresponds to the given node
      Node &at (const Node &n)
      {
        assert (hasNode (n));
        auto it = m_map.find (&n);
        assert (it != m_map.end ());
        return *(it->second);
      }
      
      /// Returns true if the node has already been cloned
      bool hasNode (const Node &n) { return m_map.count (&n) > 0; }
    };
  }
}

#endif
