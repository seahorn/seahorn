#ifndef __DSA_GRAPH_HH_
#define __DSA_GRAPH_HH_

#include <boost/core/noncopyable.hpp>
#include <boost/container/flat_map.hpp>

#include "llvm/ADT/ImmutableSet.h"

#include <string.h>
namespace llvm
{
  class Value;
  class Type;
  class DataLayout;
}

namespace seahorn
{
  namespace dsa
  {
    class Node;
    class Cell;
    class Graph
    {
      friend class Node;
    protected:
      
      typedef llvm::ImmutableSet<llvm::Type*> Set;
      typedef typename Set::Factory SetFactory;
      SetFactory m_setFactory;
      
      std::vector<std::unique_ptr<Node> > m_nodes;
      
      SetFactory &getSetFactory () { return m_setFactory; }
      Set emptySet () { return m_setFactory.getEmptySet (); }
      /// return a new set that is the union of old and a set containing v
      Set mkSet (Set old, const llvm::Type *v) { return m_setFactory.add (old, v); }

      const llvm::DataLayout &getDataLayout ();
    public:
      Node &mkNode ();
    };
    
    /** 
        A memory cell (or a field). An offset into a memory object.
     */
    class Cell
    {
      /// memory object
      mutable Node *m_node;
      /// offset
      mutable unsigned m_offset;

    public:
      Cell () : m_node(nullptr), m_offset (0) {}
      Cell (Node *node, unsigned offset) : m_node (node), m_offset (offset) {}
      Cell (const Cell &o) : m_node (o.m_node), m_offset (o.m_offset) {}
      Cell &operator= (const Cell &o)
      { m_node = o.m_node; m_offset = o.m_offset; return *this; }
      
      bool operator== (const Cell &o) const
      {return m_node == o.m_node && m_offset == o.m_offset;}
      bool operator< (const Cell &o) const
      { return m_node < o.m_node || (m_node == o.m_node && m_offset < o.m_offset); }
      
      bool isNull () const { return m_node == nullptr; }
      inline Node *getNode () const; 
      unsigned getOffset () const { return m_offset; }

      inline void pointTo (Node &n, unsigned offset);

      inline bool hasLink (unsigned offset = 0) const;
      inline const Cell &getLink (unsigned offset = 0) const;
      inline void setLink (unsigned offset, const Cell &c);
      inline void addLink (unsigned offset, Cell &c);
      
      /// unify with a given cell. At the end, both cells point to the
      /// same offset of the same node. Might cause collapse of the
      /// nodes represented by the cells.
      inline void unify (Cell &c);
      
      void swap (Cell &o)
      { std::swap (m_node, o.m_node); std::swap (m_offset, o.m_offset); }
    };
    
    
    /// A node of a DSA graph representing a memory object
    class Node : private boost::noncopyable
    {
      friend class Graph;
      friend class Cell;
      struct NodeType
      {
        unsigned shadow:1;
        unsigned alloca:1;
        unsigned heap:1;
        unsigned global:1;
        unsigned externFunc:1;
        unsigned externGlobal:1;
        unsigned unknown:1;
        unsigned incomplete:1;
        unsigned modified:1;
        unsigned read:1;
        unsigned array:1;
        unsigned collapsed:1;
        unsigned external:1;
        unsigned inttoptr:1;
        unsigned ptrtoint:1;
        unsigned vastart:1;
        unsigned dead:1;

        NodeType () {reset();}
        void join (const NodeType &n)
        {
          shadow |= n.shadow;
          alloca |= n.alloca;
          heap |= n.heap;
          global |= n.global;
          externFunc |= n.externFunc;
          externGlobal |= n.externGlobal;
          unknown |= n.unknown;
          incomplete |= n.incomplete;
          modified |= n.modified;
          read |= n.read;
          array |= n.array;
          collapsed |= n.collapsed;
          external |= n.external;
          inttoptr |= n.inttoptr;
          ptrtoint |= n.ptrtoint;
          vastart |= n.vastart;
          dead |= n.dead;
        }
        void reset () { memset (this, 0, sizeof (*this)); }
      };
      
      /// parent DSA graph
      Graph *m_graph;
      /// node marks
      struct NodeType m_nodeType;
      /// TODO: UNUSED
      mutable const llvm::Value *m_unique_scalar;
      /// When the node is forwarding, the memory cell at which the
      /// node begins in some other memory object
      Cell m_forward;

      typedef Graph::Set Set;
      typedef boost::container::flat_map<unsigned,  Set> types_type;
      typedef boost::container::flat_map<unsigned, Cell> links_type;
      /// known type of every offset/field
      types_type m_types;
      /// destination of every offset/field
      links_type m_links;
      
      /// known size
      unsigned m_size;

      Node (Graph &g) : m_graph (&g), m_unique_scalar (nullptr), m_size (0) {}
      
      /// adjust offset based on type of the node Collapsed nodes
      /// always have offset 0; for array nodes the offset is modulo
      /// array size; otherwise offset is not adjusted
      unsigned adjustOffset (unsigned offset) const
      {
        if (isCollapsed ()) return 0;
        if (isArray ()) return offset % m_size;
        return offset;
      }
      
      /// Unify a given node with a specified offset of the current node
      /// post-condition: the given node points to the current node.
      /// might cause a collapse
      inline void unifyAt (Node &n, unsigned offset);
      
      /// Transfer links/types and other information from the current
      /// node to the given one at a given offset and make the current
      /// one point to the result. Might cause collapse.  Most clients
      /// should use unifyAt() that has less stringent preconditions.
      inline void pointTo (Node &node, unsigned offset);
    public:
      /// unify with a given node
      void unify (Node &n) { unifyAt (n, 0); }
      Node &setAlloca (bool v = true) { m_nodeType.alloca = v; return *this;}
      bool isAlloca () const { return m_nodeType.alloca; }

      Node &setArray (bool v = true) { m_nodeType.array = v; return *this; }
      bool isArray () const { return m_nodeType.array; }

      Node &setCollapsed (bool v = true) { m_nodeType.collapsed = v; return *this; }
      bool isCollapsed () const { return m_nodeType.collapsed; }
      
      bool isUnique () const { return m_unique_scalar; }
      
      inline bool isForwarding () const;
      
      
      /// Return a node the current node represents. If the node is
      /// forwarding, returns the non-forwarding node this node points
      /// to. Might be expensive.
      inline Node* getNode ();
      inline const Node* getNode () const;
      inline unsigned getOffset () const;

      const types_type &types () { return m_types; }
      const links_type &links () { return m_links; }

      unsigned size () { return m_size; }
      void growSize (unsigned v) {if (v > m_size) m_size = v;}
      
      /// increase size to accommodate a field of type t at the given offset
      void growSize (unsigned offset, const llvm::Type *t);

      bool hasLink (unsigned offset) const
      { return m_links.count (adjustOffset (offset)) > 0; }
      Cell &getLink (unsigned offset)
      {return m_links [adjustOffset (offset)];}
      const Cell &getLink (unsigned offset) const
      {return m_links.at (adjustOffset (offset));}
      void setLink (unsigned offset, const Cell &c) {getLink (offset) = c;}
      inline void addLink (unsigned offset, Cell &c);

      bool hasType (unsigned offset) const
      {
        if (isCollapsed ()) return false;
        return m_types.count (adjustOffset (offset)) > 0
          && !m_types.at (adjustOffset (offset)).isEmpty ();
      }
      const Set getType (unsigned offset) const
      { return m_types.at (adjustOffset (offset));}
      bool isVoid () { return m_types.empty (); }
      bool isEmtpyType ()
      {
        return std::all_of (std::begin (m_types), std::end (m_types),
                            [] (const types_type::value_type &v)
                            { return v.second.isEmpty (); } );
      }
      /// Adds a type of a field at a given offset
      void addType (unsigned offset, const llvm::Type *t)
      {
        if (isCollapsed ()) return;
        offset = adjustOffset (offset);
        assert (offset < size ());
        growSize (offset, t);
        if (isCollapsed ()) return;
        Set types = m_graph->emptySet ();
        if (m_types.count (offset) > 0) types = m_types.at (offset);
        types = m_graph->mkSet (types, t);
        m_types.insert (std::make_pair (offset, types));
      }
      /// Adds a set of types for a field at a given offset
      void addType (unsigned offset, Set types)
      {
        if (isCollapsed ()) return;
        for (const llvm::Type *t : types) addType (offset, t);
      }
      /// joins all the types of a given node starting at a given
      /// offset of the current node
      void joinTypes (unsigned offset, const Node &n)
      {
        if (isCollapsed () || n.isCollapsed ()) return;
        for (auto &kv : n.m_types) addType (kv.first, kv.second);
      }

      /// collapse the current node. Looses all field sensitivity
      void collapse ()
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
          pointTo (n, 0);
        }
      }
    };

    bool Node::isForwarding () const
    { return !m_forward.isNull (); }

    void Node::pointTo (Node &node, unsigned offset)
    {
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
      
    void Node::addLink (unsigned offset, Cell &c)
    {
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
    void Node::unifyAt (Node &n, unsigned o)
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

      
      unsigned offset = adjustOffset (offset);
      if (&n == this)
      {
        // -- merging the node into itself at a different offset
        if (offset > 0) collapse();
        return;
      }

      
      // -- move everything from n to this node
      n.pointTo (*this, offset);
    }
    
    void Cell::unify (Cell &c)
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
      
    Node* Cell::getNode () const
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
    
    bool Cell::hasLink (unsigned offset) const
    {return m_node && getNode ()->hasLink (m_offset + offset);}

    const Cell &Cell::getLink (unsigned offset) const
    {
      assert (m_node);
      return getNode ()->getLink(offset + m_offset);
    }

    void Cell::setLink (unsigned offset, const Cell &c)
    { getNode ()->setLink(m_offset + offset, c); }

    void Cell::addLink (unsigned offset, Cell &c)
    { getNode ()->addLink (m_offset + offset, c); }
    
    void Cell::pointTo (Node &n, unsigned offset)
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
    
    Node* Node::getNode () 
    { return isForwarding () ? m_forward.getNode () : this;}

    const Node* Node::getNode () const
    { return isForwarding () ? m_forward.getNode () : this;}

    unsigned Node::getOffset () const
    {
      if (!isForwarding ()) return 0;
      m_forward.getNode ();
      return m_forward.getOffset ();
    }
    
    Node& Graph::mkNode ()
    {
      m_nodes.push_back (std::unique_ptr<Node> (new Node (*this)));
      return *m_nodes.back ();
    }
    
    // TODO: Move to .cc file and uncomment.
    // void Node::growSize (Type *t, unsigned offset)
    // {
    //   if (!t) return;
    //   if (t->isVoidTy ()) return;
    //   if (isCollapsed ()) return;

      // if (isArray ()) COLLAPSE_IF_TRYING_TO_GROW_SIZE_TWICE
    //   auto tSz = m_graph.getDataLayout ().getTypeAllocSize (t);
    //   growSize (tSz + offset);
    // }

  }
}

#endif
