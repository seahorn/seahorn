#ifndef __DSA_GRAPH_HH_
#define __DSA_GRAPH_HH_

#include <boost/core/noncopyable.hpp>
#include <boost/container/flat_map.hpp>

#include "llvm/ADT/ImmutableSet.h"
#include "llvm/ADT/DenseMap.h"

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
      
      const llvm::DataLayout &m_dl;
      typedef llvm::ImmutableSet<llvm::Type*> Set;
      typedef typename Set::Factory SetFactory;
      SetFactory m_setFactory;
      
      /// DSA nodes owned by this graph
      std::vector<std::unique_ptr<Node> > m_nodes;
      
      /// Map from scalars to cells in this graph
      llvm::DenseMap<const llvm::Value*, Cell> m_values;
      
      SetFactory &getSetFactory () { return m_setFactory; }
      Set emptySet () { return m_setFactory.getEmptySet (); }
      /// return a new set that is the union of old and a set containing v
      Set mkSet (Set old, const llvm::Type *v) { return m_setFactory.add (old, v); }

      const llvm::DataLayout &getDataLayout () const { return m_dl; }
      
      
    public:
      Graph (const llvm::DataLayout &dl) : m_dl (dl) {}
      /// remove all forwarding nodes
      void compress ();

      /// returns a cell corresponding to the value
      Cell valueCell (const llvm::Value &v);
      
      /// -- allocates a new node
      Node &mkNode ();

      Node &cloneNode (const Node &n);
      
      /// creates a cell for the value or returns existing cell if
      /// present
      Cell &mkCell (const llvm::Value &v);

      /// return a cell for the value
      const Cell &getCell (const llvm::Value &v) const;

      /// return true iff the value has a cel
      bool hasCell (const llvm::Value &v) const
      { return m_values.count (&v) > 0; }
      
      /// import the given graph into the current one
      /// copies all nodes from g and unifies all common scalars
      void import (const Graph &g);
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
      Node *getNode () const; 
      unsigned getOffset () const { return m_offset; }

      void pointTo (Node &n, unsigned offset);
      
      void pointTo (const Cell &c, unsigned offset = 0)
      {
        assert (!c.isNull ());
        Node *n = c.getNode ();
        pointTo (*n, c.getOffset () + offset);
      }

      inline bool hasLink (unsigned offset = 0) const;
      inline const Cell &getLink (unsigned offset = 0) const;
      inline void setLink (unsigned offset, const Cell &c);
      inline void addLink (unsigned offset, Cell &c);
      inline void addType (unsigned offset, const llvm::Type *t);
      
      /// unify with a given cell. At the end, both cells point to the
      /// same offset of the same node. Might cause collapse of the
      /// nodes represented by the cells.
      void unify (Cell &c);
      
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

      class Offset;
      friend class Offset;
      /// helper class to ensure that offsets are properly adjusted
      class Offset
      {
        const Node &m_node;
        const unsigned m_offset;
      public:
        Offset (const Node &n, unsigned offset) : m_node(n), m_offset(offset) {}
        operator unsigned() const; 
        const Node &node () const { return m_node; }
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

      Node (Graph &g, const Node &n, bool copyLinks = false);
      
      /// Unify a given node with a specified offset of the current node
      /// post-condition: the given node points to the current node.
      /// might cause a collapse
      void unifyAt (Node &n, unsigned offset);
      
      /// Transfer links/types and other information from the current
      /// node to the given one at a given offset and make the current
      /// one point to the result. Might cause collapse.  Most clients
      /// should use unifyAt() that has less stringent preconditions.
      void pointTo (Node &node, const Offset &offset);
      
      Cell &getLink (const Offset &offset)
      {
        assert (this == &offset.node ());
        return m_links [offset];
      }
      
      /// Adds a set of types for a field at a given offset
      void addType (const Offset &offset, Set types);
      
      /// joins all the types of a given node starting at a given
      /// offset of the current node
      void joinTypes (unsigned offset, const Node &n);
      
      /// increase size to accommodate a field of type t at the given offset
      void growSize (const Offset &offset, const llvm::Type *t);
      Node &setArray (bool v = true) { m_nodeType.array = v; return *this; }
    public:
      /// unify with a given node
      void unify (Node &n) { unifyAt (n, 0); }
      Node &setAlloca (bool v = true) { m_nodeType.alloca = v; return *this;}
      bool isAlloca () const { return m_nodeType.alloca; }

      Node &setArraySize (unsigned sz)
      {
        assert (!isArray ());
        assert (!isForwarding ());
        assert (m_size <= sz);
        
        setArray (true);
        m_size = sz;
        return *this;
      }
      
      bool isArray () const { return m_nodeType.array; }

      Node &setCollapsed (bool v = true)
      { m_nodeType.collapsed = v; setArray (false); return *this; }
      bool isCollapsed () const { return m_nodeType.collapsed; }
      
      bool isUnique () const { return m_unique_scalar; }
      
      inline bool isForwarding () const;
      
      
      Graph *getGraph () { return m_graph; } 
      const Graph *getGraph () const { return m_graph; } 
      
      /// Return a node the current node represents. If the node is
      /// forwarding, returns the non-forwarding node this node points
      /// to. Might be expensive.
      inline Node* getNode ();
      inline const Node* getNode () const;
      unsigned getOffset () const;

      const types_type &types () const { return m_types; }
      const links_type &links () const { return m_links; }

      unsigned size () const { return m_size; }
      void growSize (unsigned v);
      

      bool hasLink (unsigned offset) const
      { return m_links.count (Offset (*this, offset)) > 0; }
      const Cell &getLink (unsigned offset) const
      {return m_links.at (Offset (*this, offset));}
      void setLink (unsigned offset, const Cell &c) {getLink (Offset (*this, offset)) = c;}
      void addLink (unsigned offset, Cell &c);

      bool hasType (unsigned offset) const;
      
      const Set getType (unsigned o) const
      {
        Offset offset (*this, o);
        return m_types.at (offset);
      }
      bool isVoid () const { return m_types.empty (); }
      bool isEmtpyType () const;
      
      /// Adds a type of a field at a given offset
      void addType (unsigned offset, const llvm::Type *t);
      
      /// collapse the current node. Looses all field sensitivity
      void collapse ();
    
    };

    bool Node::isForwarding () const
    { return !m_forward.isNull (); }

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

    void Cell::addType (unsigned offset, const llvm::Type *t)
    { getNode ()->addType(m_offset + offset, t); }
    
    
    Node* Node::getNode () 
    { return isForwarding () ? m_forward.getNode () : this;}

    const Node* Node::getNode () const
    { return isForwarding () ? m_forward.getNode () : this;}
  }
}

#endif
