#ifndef __DSA_MAPPER__HH_
#define __DSA_MAPPER__HH_
#include "seahorn/Analysis/DSA/Graph.hh"

#include <unordered_map>
#include <boost/container/flat_map.hpp>

namespace seahorn
{
  namespace dsa
  {
    /** Builds a functional (one-to-many) map between two DSA graphs.
        Roots of the graphs are entered using insert() method.
        Requires that a function map exists
    */
    class FunctionalMapper {
      std::unordered_map<Cell, Cell> m_cells;
      std::unordered_map<const Node*, Cell> m_nodes;

    public:
      FunctionalMapper () {}

      void insert (const Cell &src, const Cell &dst);

      Cell get (const Node &n) const
      {return m_nodes.count(&n) ? m_nodes.at (&n) : Cell();}
      
      Cell get (const Cell &c) const
      {return m_cells.count (c) ? m_cells.at (c) : Cell();}
    };

    class SimulationMapper 
    {
      /// the simulation relation: a node is simulated by a cell
      typedef std::unordered_map<const Node*,
                                 boost::container::flat_map<Node*,
                                                            unsigned> > rel_type;
      rel_type m_sim;

    public:

      SimulationMapper () {}

      bool insert (const Cell &c1, Cell &c2);
      bool insert (const Node &n1, Node &n2, unsigned offset);

      Cell get (const Node &n) const
      {
        if (!m_sim.count (&n)) return Cell ();
        auto &map = m_sim.at (&n);

        if (map.size () != 1) return Cell ();
        
        auto kv = map.begin ();
        return Cell (*kv->first, kv->second);
      }
      
      Cell get (const Cell &c) const
      {
        if (!c.getNode ()) return Cell();
        
        Cell res = get (*c.getNode ());
        return Cell (res.getNode (),
                     res.getOffset () + c.getOffset ());
      }

      bool empty () const { return m_sim.empty (); }

      // Return true if no cell can simulate more than one node
      bool isInjective (bool onlyModified = true) const;

      // Return true if each node is simulated by at most one cell
      bool isFunction () const;

      void write (llvm::raw_ostream &o) const ;

    };
  }
}
#endif
