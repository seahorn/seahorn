#include "seahorn/Analysis/DSA/Graph.hh"

#include "llvm/IR/Type.h"
#include "llvm/IR/DataLayout.h"

#include <string.h>

using namespace seahorn;
using namespace llvm;

/// adjust offset based on type of the node Collapsed nodes
/// always have offset 0; for array nodes the offset is modulo
/// array size; otherwise offset is not adjusted
dsa::Node::Offset::operator unsigned() const 
{
  if (m_node.isCollapsed ()) return 0;
  if (m_node.isArray ()) return m_offset % m_node.size ();
  return m_offset;
}

void dsa::Node::growSize (const Offset &offset, const llvm::Type *t)
{
  if (!t) return;
  if (t->isVoidTy ()) return;
  if (isCollapsed ()) return;

  if (isArray ()) assert (false && "COLLAPSE_IF_TRYING_TO_GROW_SIZE_TWICE");
  assert (m_graph);
  // XXX for some reason getTypeAllocSize() is not marked as preserving const
  auto tSz = m_graph->getDataLayout ().getTypeAllocSize (const_cast<Type*>(t));
  growSize (tSz + offset);
}

bool dsa::Node::isEmtpyType () const
{
  return std::all_of (std::begin (m_types), std::end (m_types),
                      [] (const types_type::value_type &v)
                      { return v.second.isEmpty (); } );
}

bool dsa::Node::hasType (unsigned o) const
{
  if (isCollapsed ()) return false;
  Offset offset(*this, o);
  return m_types.count (offset) > 0 && !m_types.at (offset).isEmpty ();
}

void dsa::Node::addType (unsigned o, const llvm::Type *t)
{
  if (isCollapsed ()) return;
  Offset offset (*this, o);
  assert (offset < size ());
  growSize (offset, t);
  if (isCollapsed ()) return;
  Set types = m_graph->emptySet ();
  if (m_types.count (offset) > 0) types = m_types.at (offset);
  types = m_graph->mkSet (types, t);
  m_types.insert (std::make_pair ((unsigned)offset, types));
}

void dsa::Node::addType (const Offset &offset, Set types)
{
  if (isCollapsed ()) return;
  for (const llvm::Type *t : types) addType (offset, t);
}

void dsa::Node::joinTypes (unsigned offset, const Node &n)
{
  if (isCollapsed () || n.isCollapsed ()) return;
  for (auto &kv : n.m_types)
  {
    const Offset noff (*this, kv.first + offset);
    addType (noff, kv.second);
  }
}

/// collapse the current node. Looses all field sensitivity
void dsa::Node::collapse ()
{
  if (isCollapsed ()) return;
        
  // if the node is already of smallest size, just mark it
  // collapsed to indicate that it cannot grow or change
  if (size () <= 1)
  {
    m_size = 1;
    setCollapsed (true);
    return;
  }
  else
  {
    // create a new node to be the collapsed version of the current one
    // move everything to the new node. This breaks cycles in the links.
    Node &n = m_graph->mkNode ();
    n.m_nodeType.join (m_nodeType);
    n.setCollapsed (true);
    n.m_size = 1;
    pointTo (n, Offset(n, 0));
  }
}

void dsa::Node::pointTo (Node &node, const Offset &offset)
{
  assert (&node == &offset.node ());
  assert (&node != this);
  assert (!isForwarding ());
      
  unsigned sz = size ();
      
  // -- create forwarding link
  m_forward.pointTo (node, offset);
  // -- get updated offset based on how forwarding was resolved
  unsigned noffset = m_forward.getOffset ();
  // -- at this point, current node is being embedded at noffset
  // -- into node
      
  // -- grow the size if necessary
  if (sz + noffset > node.size ()) node.growSize (sz + noffset);
  
  // -- merge the types
  node.joinTypes (noffset, *this);
      
  // -- merge node annotations
  node.m_nodeType.join (m_nodeType);
      

  // -- move all the links
  for (auto &kv : m_links)
  {
    if (kv.second.isNull ()) continue;
    m_forward.addLink (kv.first, kv.second);
        
  }
      
  // reset current node
  m_size = 0;
  m_links.clear ();
  m_types.clear ();
  m_unique_scalar = nullptr;
  m_nodeType.reset ();
}

void dsa::Node::addLink (unsigned o, Cell &c)
{
  Offset offset (*this, o);
  if (!hasLink (offset))
    setLink (offset, c);
  else
  {
    Cell &link = getLink (offset);
    link.unify (c);
  }
}
      
/// Unify a given node into the current node at a specified offset.
/// Might cause collapse. 
void dsa::Node::unifyAt (Node &n, unsigned o)
{
  assert (!isForwarding ());
  assert (!n.isForwarding ());
      
  // collapse before merging with a collapsed node
  if (n.isCollapsed ()) collapse ();
      
  if (// aggressively collapse arrays. This can be refined
      (isArray () != n.isArray ()) ||
      // aggressively collapse arrays of different size
      ( isArray () && n.isArray () && size () != n.size ()))
  {
    collapse ();
    n.collapse ();
  }

      
  Offset offset (*this, o);
  if (&n == this)
  {
    // -- merging the node into itself at a different offset
    if (offset > 0) collapse();
    return;
  }

      
  // -- move everything from n to this node
  n.pointTo (*this, offset);
}
    
void dsa::Cell::unify (Cell &c)
{
  if (isNull ())
  {
    assert (!c.isNull ());
    pointTo (*c.getNode (), c.getOffset ());
  }
  else if (c.isNull ())
    c.unify (*this);
  else
  {
    Node &n1 = *getNode ();
    unsigned o1 = getOffset ();
        
    Node &n2 = *c.getNode ();
    unsigned o2 = c.getOffset ();

    if (o1 < o2)
      n2.unifyAt (n1, o2 - o1);
    else if (o2 < o1)
      n1.unifyAt (n2, o1 - o2);
    else /* o1 == o2 */
      // TODO: other ways to break ties
      n1.unify (n2);
  }
}
      
dsa::Node* dsa::Cell::getNode () const
{
  if (isNull ()) return nullptr;
      
  Node *n = m_node->getNode ();
  if (n != m_node)
  {
    assert (m_node->isForwarding ());
    m_node = n;
    m_offset += m_node->getOffset ();
  }
  return m_node;
}


void dsa::Cell::pointTo (Node &n, unsigned offset)
{
  assert (!n.isForwarding ());
  m_node = &n;
  if (n.isCollapsed ()) m_offset = 0;
  else if (n.size () == 0) { assert (false); m_offset = 1; }
  else if (n.isArray ()) m_offset = offset % n.size ();
  else
  {
    assert (offset < n.size ());
    m_offset = offset;
  }
}    

unsigned dsa::Node::getOffset () const
{
  if (!isForwarding ()) return 0;
  m_forward.getNode ();
  return m_forward.getOffset ();
}


dsa::Node& dsa::Graph::mkNode ()
{
  m_nodes.push_back (std::unique_ptr<Node> (new Node (*this)));
  return *m_nodes.back ();
}
