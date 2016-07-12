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
