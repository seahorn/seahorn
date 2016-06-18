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
      Set setAdd (Set old, const llvm::Type *v) { return m_setFactory.add (old, v); }
      Set setDel (Set old, const llvm::Type *v) { return m_setFactory.remove (old, v); }

      const llvm::DataLayout &getDataLayout ();
    public:
      Node &mkNode ();
    };
    
    class Cell
    {
      mutable Node *m_node;
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
      
      void swap (Cell &o)
      { std::swap (m_node, o.m_node); std::swap (m_offset, o.m_offset); }
    };
    
    
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
      
      Graph *m_graph;
      struct NodeType m_nodeType;
      mutable const llvm::Value *m_unique_scalar;
      Cell m_forward;

      typedef Graph::Set Set;
      typedef boost::container::flat_map<unsigned,  Set> types_type;
      typedef boost::container::flat_map<unsigned, Cell> links_type;
      types_type m_types;
      links_type m_links;
      
      unsigned m_size;

      Node (Graph &g) : m_graph (&g), m_unique_scalar (nullptr), m_size (0) {}
    public:
      Node &setAlloca (bool v = true) { m_nodeType.alloca = v; return *this;}
      bool isAlloca () { return m_nodeType.alloca; }

      Node &setArray (bool v = true) { m_nodeType.array = v; return *this; }
      bool isArray () { return m_nodeType.array; }

      Node &setCollapsed (bool v = true) { m_nodeType.collapsed = v; return *this; }
      bool isCollapsed () { return m_nodeType.collapsed; }
      
      bool isUnique () { return m_unique_scalar; }
      
      inline bool isForwarding () const;
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
      { return m_links.count (offset) > 0; }
      Cell &getLink (unsigned offset)
      { assert (offset < size ()); return m_links[offset]; }
      const Cell &getLink (unsigned offset) const { return m_links.at (offset); }
      void setLink (unsigned offset, const Cell &c) {getLink (offset) = c;}

      bool hasType (unsigned offset) const
      { return m_types.count (offset) > 0 && !m_types.at (offset).isEmpty (); }
      const Set getType (unsigned offset) const
      { return m_types.at (offset); }
      bool isVoid () { return m_types.empty (); }
      bool isEmtpyType ()
      {
        return std::all_of (std::begin (m_types), std::end (m_types),
                            [] (const types_type::value_type &v)
                            { return v.second.isEmpty (); } );
      }
      void addType (unsigned offset, const llvm::Type *t)
      {
        assert (offset < size ());
        growSize (offset, t);
        Set types = m_graph->emptySet ();
        if (m_types.count (offset) > 0) types = m_types.at (offset);
        types = m_graph->setAdd (types, t);
        m_types.insert (std::make_pair (offset, types));
      }
      void addType (unsigned offset, Set types)
      {for (const llvm::Type *t : types) addType (offset, t);}
      void mergeTypes (unsigned offset, const Node &n)
      {for (auto &kv : n.m_types) addType (kv.first, kv.second);}
    };

    bool Node::isForwarding () const
    { return !m_forward.isNull (); }

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
    
    // void Node::growSize (Type *t, unsigned offset)
    // {
    //   if (!t) return;
    //   if (t->isVoidTy ()) return;
    //   if (isCollapsed ()) return;

    //   if (isArray () && size () > 0) { offset %= size (); }
    //   auto tSz = m_graph.getDataLayout ().getTypeAllocSize (t);
    //   growSize (tSz + offset);
    // }

  }
}

#endif
