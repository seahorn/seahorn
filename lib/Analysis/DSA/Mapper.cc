#include "seahorn/Analysis/DSA/Mapper.hh"
#include "llvm/Support/raw_ostream.h"

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

  if (c2.getNode()->isCollapsed())
    return insert (*c1.getNode (), *c2.getNode (), 0);

  // XXX: adjust the offsets
  Node::Offset o1 (*c1.getNode(), c1.getOffset());
  Node::Offset o2 (*c2.getNode(), c2.getOffset());
    
  if (o2 < o1)
  { m_sim.clear (); return false; }
  
  return insert (*c1.getNode (), *c2.getNode (), o2 - o1);
}

bool SimulationMapper::insert (const Node &n1, Node &n2, unsigned o)
{
  // XXX: adjust the offset
  Node::Offset offset (n2, o);

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
    if (offset > 0 && n1.size () + o > n2.size ())
      { m_sim.clear (); return false; }
  }

  // XXX: a collapsed node can simulate an array node
  if (n1.isArray () && (!n2.isArray () && !n2.isCollapsed()))
  { m_sim.clear (); return false; }

  if (n1.isArray () && offset != 0)
  { m_sim.clear (); return false; } 
    
  // XXX: a collapsed node can simulate an array node
  if (n1.isArray () && !n2.isCollapsed() && n1.size () != n2.size ())
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

    if (off2 < off1 && !n4->isCollapsed ())
    { m_sim.clear (); return false; }
    
    if (!insert (*n3, *n4, off2 - off1))
    { map.clear (); return false; }
  }
  
  return true;
}

void SimulationMapper::write(llvm::raw_ostream&o) const 
{
  o << "BEGIN simulation mapper\n";
  for (auto &kv: m_sim)
    for (auto &c: kv.second) 
      o << "(" << *(kv.first) << ", " << *(c.first) << ", " << c.second << ")\n";
  o << "END  simulation mapper\n";
}

bool SimulationMapper::isInjective (bool onlyModified)  const 
{
  boost::container::flat_set<Cell> inv_sim;
  for (auto &kv: m_sim) 
    for (auto &c: kv.second) 
    {
      auto res = inv_sim.insert(Cell(c.first, c.second));
      if (!onlyModified || c.first->isModified()) 
        if (!res.second) return false;
    }
  return true;
}

bool SimulationMapper::isFunction () const 
{
  for (auto &kv: m_sim)
    if (kv.second.size () > 1) return false;
  return true;
}
