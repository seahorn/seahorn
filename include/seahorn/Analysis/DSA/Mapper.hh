#ifndef __DSA_MAPPER__HH_
#define __DSA_MAPPER__HH_
#include "seahorn/Analysis/DSA/Graph.hh"

#include <unordered_map>

namespace seahorn
{
  namespace dsa
  {
    /** Builds a functional (one-to-many) map between two DSA graphs.
        Roots of the graphs are entered using insert() method.
        Requires that a function map exists
    */
    class FunctionalMapper { std::unordered_map<Cell, Cell> m_cells;
    std::unordered_map<const Node*, Cell> m_nodes;

    public:
      FunctionalMapper () {}

      void insert (const Cell &src, const Cell &dst);

      Cell get (const Node &n) const
      {return m_nodes.count(&n) ? m_nodes.at (&n) : Cell();}
      
      Cell get (const Cell &c) const
      {return m_cells.count (c) ? m_cells.at (c) : Cell();}
    };
  }
}
#endif
