#include "seahorn/Analysis/DSA/Mapper.hh"

using namespace seahorn;
using namespace seahorn::dsa;

void FunctionalMapper::insert (const Cell &src, const Cell &dst)
{
  assert (!src.isNull ());
  assert (!dst.isNull ());

  // -- already mapped
  Cell res = get (src);
  if (!res.isNull ()) return;

  res = get (*src.getNode ());
  if (!res.isNull ())
    assert (res.getNode () == dst.getNode () && "No functional node mapping");
  
  assert (src.getOffset () <= dst.getOffset () && "Not supported");

  // -- offset of the source node in the destination
  unsigned srcNodeOffset = dst.getOffset () - src.getOffset ();
  
  m_nodes.insert (std::make_pair (src.getNode (), Cell (dst.getNode (), srcNodeOffset)));
  m_cells.insert (std::make_pair (src, dst));
  
  Node::Offset srcOffset (*src.getNode (), src.getOffset ());
  
  // -- process all the links
  // XXX Don't think this properly handles aligning array nodes of different sizes
  for (auto &kv : src.getNode ()->links ())
  {
    if (kv.first < srcOffset) continue;
    if (dst.getNode ()->hasLink (srcNodeOffset + kv.first))
      insert (*kv.second, dst.getNode ()->getLink (srcNodeOffset + kv.first));
  }
}

bool SimulationMapper::insert (const Cell &c1, Cell &c2)
{
  if (c1.isNull () != c2.isNull ())
  { m_sim.clear (); return false; }

  if (c1.isNull ()) return true;

  if (c2.getOffset () < c1.getOffset ())
  { m_sim.clear (); return false; }
  
  return insert (*c1.getNode (), *c2.getNode (),
                 c2.getOffset () - c1.getOffset ());
}

bool SimulationMapper::insert (const Node &n1, Node &n2, unsigned offset)
{
  auto &map = m_sim[&n1];
  if (map.count (&n2) > 0)
  {
    if (map.at (&n2) == offset) return true;
    m_sim.clear (); return false;
  }

  // -- not array can be simulated by array of larger size at offset 0
  // XXX probably sufficient if n1 can be completely embedded into n2,
  // XXX not necessarily at offset 0
  if (!n1.isArray () && n2.isArray ())
  {
    if (offset > 0 || n1.size () > n2.size ())
    { m_sim.clear (); return false; }
  }
  
  if (n1.isArray () != n2.isArray ())
  { m_sim.clear (); return false; }

  if (n1.isArray () && offset != 0)
  { m_sim.clear (); return false; } 
  
  if (n1.isArray () && n1.size () != n2.size ())
  { m_sim.clear (); return false; }
  
  if (n1.isCollapsed () && !n2.isCollapsed ())
  { m_sim.clear (); return false; }
  
  // add n2 into the map
  map[&n2] = offset;

  // check children
  for (auto &kv : n1.links ())
  {
    Node *n3 = kv.second->getNode ();
    unsigned off1 = kv.second->getOffset ();

    unsigned j = n2.isCollapsed () ? 0 : kv.first + offset;
    if (!n2.hasLink (j))
    { m_sim.clear (); return false; }

    auto &link = n2.getLink (j);
    Node *n4 = link.getNode ();
    unsigned off2 = link.getOffset ();

    if (off2 < off1)
    { m_sim.clear (); return false; }
    
    if (!insert (*n3, *n4, off2 - off1))
    { map.clear (); return false; }
  }
  
  return true;
}

bool SimulationMapper::isOneToMany (bool onlyModified)  const 
{
  boost::container::flat_set<Cell> inv_sim;
  for (auto &kv: m_sim) 
    for (auto &c: kv.second) 
    {
      auto res = inv_sim.insert(Cell(c.first, c.second));
      if (!onlyModified || c.first->isModified()) 
        if (res.second) return false;
    }
  return true;
}
