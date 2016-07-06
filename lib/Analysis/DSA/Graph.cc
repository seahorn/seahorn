#include "seahorn/Analysis/DSA/Graph.hh"

#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Argument.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/GlobalAlias.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"

#include <string>
#include <set>

#include "seahorn/Analysis/DSA/Cloner.hh"

#include "avy/AvyDebug.h"

using namespace seahorn;
using namespace llvm;


dsa::Node::Node (Graph &g, const Node &n, bool copyLinks) :
  m_graph (&g), m_unique_scalar (n.m_unique_scalar), m_size (n.m_size)
{
  assert (!n.isForwarding ());
  
  // -- copy node type info
  m_nodeType = n.m_nodeType;
  
  // -- copy types
  joinTypes (0, n);

  // -- copy links
  if (copyLinks)
  {
    assert (n.m_graph == m_graph);
    for (auto &kv : n.m_links)
      m_links[kv.first].reset (new Cell (*kv.second));
  }
}
/// adjust offset based on type of the node Collapsed nodes
/// always have offset 0; for array nodes the offset is modulo
/// array size; otherwise offset is not adjusted
dsa::Node::Offset::operator unsigned() const 
{
  if (m_node.isCollapsed ()) return 0;
  if (m_node.isArray ()) return m_offset % m_node.size ();
  return m_offset;
}

void dsa::Node::growSize (unsigned v)
{
  if (isCollapsed ()) m_size = 1;
  else if (v > m_size)
  {
    // -- cannot grow size of an array
    if (isArray ()) collapse ();
    else m_size = v;
  }
}

void dsa::Node::growSize (const Offset &offset, const llvm::Type *t)
{
  if (!t) return;
  if (t->isVoidTy ()) return;
  if (isCollapsed ()) return;
  
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
    if (kv.second->isNull ()) continue;
    m_forward.addLink (kv.first, *kv.second);
    
        
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
  if (!isCollapsed () && n.isCollapsed ())
  {
    collapse ();
    getNode ()->unifyAt (n, o);
    return;
  }
    
  
      
  Offset offset (*this, o);
  if (!isCollapsed () && !n.isCollapsed () && n.isArray () && !isArray ())
  {
    // -- merge into array at offset 0
    if (offset == 0)
    {
      n.unifyAt (*this, 0);
      return;
    }
    // -- cannot merge array at non-zero offset
    else
    {
      collapse ();
      getNode ()->unifyAt (n, o);
      return;
    }
  }
  else if (isArray () && n.isArray ())
  {
    // merge larger sized array into 0 offset of the smaller array
    // if the size are compatible
    Node *min = size () <= n.size () ? this : &n;
    Node *max = min == this ? &n : this;
    
    // sizes are incompatible modulo does not distribute. Hence, we
    // can only shrink an array if the new size is a divisor of all
    // previous non-constant indexes
    if (max->size () % min->size () != 0)
    {
      collapse ();
      getNode ()->unifyAt (n, o);
      return;
    }
    else
    {
      Offset minoff (*min, o);
      // -- arrays can only be unified at offset 0
      if (minoff == 0)
      {
        if (min != this)
        {
          // unify by merging into smaller array
          n.unifyAt (*this, 0);
          return;
        }
        // otherwise, proceed unifying n into this
      }
      else
      {
        // -- cannot unify arrays at non-zero offset
        collapse ();
        getNode ()->unifyAt (n, o);
        return;
      }
    }
  }
  else if (isArray () && !n.isArray ())
  {
    // merge non-array into array at offset 0
    if (offset != 0)
    {
      collapse ();
      getNode ()->unifyAt (n, o);
      return;
    }
  }
      
  if (&n == this)
  {
    // -- merging the node into itself at a different offset
    if (offset > 0) collapse();
    return;
  }

  assert (!isForwarding ());
  assert (!n.isForwarding ());
  // -- move everything from n to this node
  n.pointTo (*this, offset);
}

void dsa::Node::writeTypes(raw_ostream&o) const {
  if (isCollapsed()) 
    o << "collapsed";
  else 
  {
    // Go through all the types, and just print them.
    const types_type & ts = types ();
    bool firstType = true;
    o << "types={";
    if (ts.begin() != ts.end()) {
      for (typename types_type::const_iterator ii = ts.begin(),
               ee = ts.end(); ii != ee; ++ii) {
        if (!firstType) o << ",";
        firstType = false;
        o << ii->first << ":"; // offset
        if (ii->second.begin () != ii->second.end()) {
          bool first = true;
          for (const Type * t: ii->second) {
            if (!first) o << "|";
            t->print(o);
            first = false;
          }
        }
        else
          o << "void";
      }
    }
    else {
      o << "void";
    }
    o << "}";
  }
  
  // XXX: this is already printed as a flag
  //if (isArray()) o << " array";
}

void dsa::Node::write(raw_ostream&o) const {
  /// XXX: we print here the address. Therefore, it will change from
  /// one run to another.
  /// TODO: assign a unique identifier based on some representative
  /// (among all referrers).

  o << "Node " << this << ": ";
  o << "flags=[" << m_nodeType.toStr() << "] ";
  writeTypes(o);

  // TODO: print links
}


void dsa::Cell::dump() const {
  write(errs());
  errs () << "\n";
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
  else if (n.isArray ())
  {
    assert (n.size () > 0);
    m_offset = offset % n.size ();
  }
  else
  {
    /// grow size as needed. allow offset to go one byte past size
    if (offset < n.size ()) n.growSize (offset);
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

dsa::Node &dsa::Graph::cloneNode (const Node &n)
{
  m_nodes.push_back (std::unique_ptr<Node> (new Node (*this, n, false)));
  return *m_nodes.back ();
}

void dsa::Graph::compress ()
{
  // -- resolve all forwarding
  for (auto &n : m_nodes)
  {
    // resolve the node
    n->getNode ();
    // if not forwarding, resolve forwarding on all links
    if (!n->isForwarding ())
      for (auto &kv : n->links ()) kv.second->getNode ();
  }

  for (auto &kv : m_values) kv.second->getNode ();
  
  // at this point, all cells and all nodes have their links
  // resolved. Every link points directly to the representative of the
  // equivalence class. All forwarding nodes can now be deleted since
  // they have no referrers.
  
  // -- remove forwarding nodes using remove-erase idiom
  m_nodes.erase (std::remove_if (m_nodes.begin(), m_nodes.end(),
                                 [] (const std::unique_ptr<Node> &n)
                                 { return n->isForwarding (); }),
                 m_nodes.end ());
}

dsa::Cell &dsa::Graph::mkCell (const llvm::Value &v, const Cell &c)
{
  // Pretend that global values are always present
  if (isa<GlobalValue> (&v) && c.isNull ())
    return mkCell (v, Cell (mkNode (), 0));
  
  auto &res = isa<Argument> (v) ? m_formals[cast<const Argument>(&v)] : m_values [&v];
  if (!res) res.reset (new Cell (c));
  return *res;
}

dsa::Cell &dsa::Graph::mkRetCell (const llvm::Function &fn, const Cell &c)
{
  auto &res = m_returns[&fn];
  if (!res) res.reset (new Cell (c));
  return *res;
}

const dsa::Cell &dsa::Graph::getCell (const llvm::Value &v) 
{
  // -- try m_formals first
  if (const llvm::Argument *arg = dyn_cast<const Argument> (&v))
  {
    auto it = m_formals.find (arg);
    assert (it != m_formals.end ());
    return *(it->second);
  }
  else if (isa<GlobalValue> (&v))
    return mkCell (v, Cell ());
  else 
  {
    auto it = m_values.find (&v);
    assert (it != m_values.end ());
    return *(it->second);
  }
}

bool dsa::Graph::hasCell (const llvm::Value &v) const
{
  return
    // -- globals are always implicitly present
    isa<GlobalValue> (&v) || 
    m_values.count (&v) > 0 ||
    (isa<Argument> (&v) &&
     m_formals.count (cast<const Argument>(&v)) > 0 );
}


void dsa::Cell::write(raw_ostream&o) const {
  o << "<" << m_offset << ",";
  m_node->write(o);
  o << ">";
}

void dsa::Node::dump() const {
  write(errs());
}

void dsa::Graph::import (const Graph &g, bool withFormals)
{
  Cloner C (*this);
  for (auto &kv : g.m_values)
  {
    // -- clone node
    Node &n = C.clone (*kv.second->getNode ());
    
    // -- re-create the cell 
    Cell c (n, kv.second->getOffset ());
    
    // -- insert value
    Cell &nc = mkCell (*kv.first, Cell ());
    
    // -- unify the old and new cells
    nc.unify (c);
  }

  if (withFormals)
  {
    for (auto &kv : g.m_formals)
    {
      Node &n = C.clone (*kv.second->getNode ());
      Cell c (&n, kv.second->getOffset ());
      Cell &nc = mkCell (*kv.first, Cell ());
      nc.unify (c);
    }
    for (auto &kv : g.m_returns)
    {
      Node &n = C.clone (*kv.second->getNode ());
      Cell c (&n, kv.second->getOffset ());
      Cell &nc = mkRetCell (*kv.first, Cell ());
      nc.unify (c);
    }
  }

  // possibly created many indirect links, compress 
  compress ();
}


void dsa::Graph::write (raw_ostream&o) const{

  typedef std::set<const llvm::Value*> ValSet;
  typedef std::set<const llvm::Argument*> ArgSet;
  typedef std::set<const llvm::Function*> FuncSet;
  typedef std::set<const Node*> NodeSet;

  typedef DenseMap<const Cell*, ValSet> CellValMap;
  typedef DenseMap<const Cell*, ArgSet> CellArgMap;
  typedef DenseMap<const Cell*, FuncSet> CellRetMap;

  // -- here all nodes referenced by scalars, formals, or returns
  NodeSet refNodes;

  // --- collect all nodes and cells referenced by scalars
  CellValMap scalarCells;
  for (auto &kv : m_values) {
    const Cell* C = kv.second.get ();
    refNodes.insert(C->getNode());
    auto it = scalarCells.find(C);
    if (it == scalarCells.end()) {
      ValSet S;
      S.insert(kv.first);
      scalarCells.insert (std::make_pair(C, S));
    } else {
      it->second.insert(kv.first);
    }
  }

  // --- collect all nodes and cells referenced by function formal
  //     parameters
  CellArgMap argCells;
  for (auto &kv : m_formals) {
    const Cell* C = kv.second.get();
    refNodes.insert(C->getNode());
    auto it = argCells.find(C);
    if (it == argCells.end()) {
      ArgSet S;
      S.insert(kv.first);
      argCells.insert (std::make_pair(C, S));
    } else {
      it->second.insert(kv.first);
    }
  }
  
  // --- collect all nodes and cells referenced by return parameters
  CellRetMap retCells;
  for (auto &kv : m_returns) {
    const Cell* C = kv.second.get();
    refNodes.insert(C->getNode());
    auto it = retCells.find(C);
    if (it == retCells.end()) {
      FuncSet S;
      S.insert(kv.first);
      retCells.insert (std::make_pair(C, S));
    } else {
      it->second.insert(kv.first);
    }
  }

  // --- print referenced nodes
  o << "=== NODES\n";
  for (auto N: refNodes) {
    N->write(o);
    o << "\n";
  }

  // TODO: print cells sorted first by node and then by offsets
  // --- print aliasing sets
  o << "=== ALIAS SETS\n";
  for (auto &kv: scalarCells) {
    const Cell * C = kv.first;
    if (kv.second.begin() != kv.second.end()) {
      o << "cell=(" << C->getNode() << "," << C->getOffset () << ")\n";
      for (const Value* V: kv.second) {
        o << "\t" << *V << "\n";
      }
    }
  }
  for (auto &kv: argCells) {
    const Cell * C = kv.first;
    if (kv.second.begin() != kv.second.end()) {
      o << "cell=(" << C->getNode() << "," << C->getOffset () << ")\n";
      for (const Argument* A: kv.second) {
        o << "\t" << *A << "\n";
      }
    }
  }
  for (auto &kv: retCells) {
    const Cell * C = kv.first;
    if (kv.second.begin() != kv.second.end()) {
      o << "cell=(" << C->getNode() << "," << C->getOffset () << ")\n";
      for (const Function* F: kv.second) {
        o << "\t" << "ret("<< F->getName() << ")\n";
      }
    }
  }
}
