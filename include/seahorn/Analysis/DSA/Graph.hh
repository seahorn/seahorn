#ifndef __DSA_GRAPH_HH_
#define __DSA_GRAPH_HH_

#include <boost/container/flat_map.hpp>
#include <boost/container/flat_set.hpp>
#include <boost/iterator/indirect_iterator.hpp>
#include "boost/iterator/filter_iterator.hpp"
#include <boost/functional/hash.hpp>

#include "llvm/ADT/ImmutableSet.h"
#include "llvm/ADT/DenseMap.h"

#include <functional>

namespace llvm
{
  class Value;
  class Type;
  class DataLayout;
  class Argument;
  class Function;
  class raw_ostream;
}

namespace seahorn
{
  namespace dsa
  {
    class Node;
    class Cell;
    class SimulationMapper;
    typedef std::unique_ptr<Cell> CellRef;
    
    class FunctionalMapper;
    class DsaCallSite;

    // Data structure graph traversal iterator
    template<typename T>
    class NodeIterator;          
    
    class Graph
    {
      friend class Node;
    public:
      typedef llvm::ImmutableSet<llvm::Type*> Set;
      typedef typename Set::Factory SetFactory;
    protected:
      
      const llvm::DataLayout &m_dl;
      SetFactory &m_setFactory;
      /// DSA nodes owned by this graph
      typedef std::vector<std::unique_ptr<Node> > NodeVector;
      NodeVector m_nodes;
            
      /// Map from scalars to cells in this graph
      typedef llvm::DenseMap<const llvm::Value*, CellRef> ValueMap;
      ValueMap m_values;

      /// Map from formal arguments to cells
      typedef llvm::DenseMap<const llvm::Argument*, CellRef> ArgumentMap;
      ArgumentMap m_formals;
      
      /// Map from formal returns of functions to cells
      typedef llvm::DenseMap<const llvm::Function*, CellRef> ReturnMap;
      ReturnMap m_returns;
      
      SetFactory &getSetFactory () { return m_setFactory; }
      Set emptySet () { return m_setFactory.getEmptySet (); }
      /// return a new set that is the union of old and a set containing v
      Set mkSet (Set old, const llvm::Type *v) { return m_setFactory.add (old, v); }

      const llvm::DataLayout &getDataLayout () const { return m_dl; }
      
      struct IsGlobal 
      {bool operator() (const ValueMap::value_type &kv) const;};
      
    public:

      Graph (const llvm::DataLayout &dl, SetFactory &sf) : m_dl (dl), m_setFactory (sf) {}
      /// remove all forwarding nodes
      void compress ();

      /// -- allocates a new node
      Node &mkNode ();

      Node &cloneNode (const Node &n);

      /// iterate over nodes
      typedef boost::indirect_iterator<typename NodeVector::const_iterator> const_iterator;
      typedef boost::indirect_iterator<typename NodeVector::iterator> iterator; 
      const_iterator begin() const;
      const_iterator end() const;
      iterator begin();
      iterator end();
      
      /// iterate over scalars
      typedef ValueMap::const_iterator scalar_const_iterator; 
      scalar_const_iterator scalar_begin() const;
      scalar_const_iterator scalar_end() const;

      typedef boost::filter_iterator<IsGlobal,
                                     typename ValueMap::const_iterator>
      global_const_iterator;
      global_const_iterator globals_begin () const;
      global_const_iterator globals_end () const;
      
      /// iterate over formal parameters of functions
      typedef ArgumentMap::const_iterator formal_const_iterator; 
      formal_const_iterator formal_begin() const;
      formal_const_iterator formal_end() const;

      /// iterate over returns of functions
      typedef ReturnMap::const_iterator return_const_iterator; 
      return_const_iterator return_begin() const;
      return_const_iterator return_end() const;
      /// creates a cell for the value or returns existing cell if
      /// present
      Cell &mkCell (const llvm::Value &v, const Cell &c);
      Cell &mkRetCell (const llvm::Function &fn, const Cell &c);

      /// return a cell for the value
      const Cell &getCell (const llvm::Value &v);

      /// return true iff the value has a cel
      bool hasCell (const llvm::Value &v) const;
      
      bool hasRetCell (const llvm::Function &fn) const
      { return m_returns.count (&fn) > 0; }

      Cell &getRetCell (const llvm::Function &fn); 

      const Cell &getRetCell (const llvm::Function &fn) const; 

      /// compute a map from callee nodes to caller nodes
      // 
      /// XXX: we might want to make the last argument a template
      /// parameter but then the definition should be in a header file.
      static bool computeCalleeCallerMapping (const DsaCallSite &cs, 
                                              Graph& calleeG, Graph& callerG,
                                              SimulationMapper& simMap,
					      const bool reportIfSanityCheckFailed = true);
      
      /// import the given graph into the current one
      /// copies all nodes from g and unifies all common scalars
      void import (const Graph &g, bool withFormals = false);

      /// pretty-printer of a graph
      void write(llvm::raw_ostream&o) const;
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
      Cell (Node &node, unsigned offset) : m_node (&node), m_offset (offset) {}
      Cell (const Cell &o, unsigned offset = 0) :
        m_node (o.m_node), m_offset (o.m_offset + offset) {}
      Cell &operator= (const Cell &o)
      { m_node = o.m_node; m_offset = o.m_offset; return *this; }
      
      bool operator== (const Cell &o) const
      {return m_node == o.m_node && m_offset == o.m_offset;}
      bool operator!= (const Cell &o) const
      { return !operator==(o); }
      bool operator< (const Cell &o) const
      { return m_node < o.m_node || (m_node == o.m_node && m_offset < o.m_offset); }

      void setRead (bool v = true);
      void setModified (bool v = true);
      
      bool isRead () const;
      bool isModified () const;
      
      bool isNull () const { return m_node == nullptr; }
      Node *getNode () const;
      // for internal Dsa use (actual offset)
      unsigned getRawOffset () const;
      // for Dsa clients (offset is adjusted based on the node)
      unsigned getOffset () const;       

      void pointTo (Node &n, unsigned offset);
      
      void pointTo (const Cell &c, unsigned offset = 0)
      {
        assert (!c.isNull ());
        Node *n = c.getNode ();
        pointTo (*n, c.getRawOffset () + offset);
      }

      inline bool hasLink (unsigned offset = 0) const;
      inline const Cell &getLink (unsigned offset = 0) const;
      inline void setLink (unsigned offset, const Cell &c);
      inline void addLink (unsigned offset, Cell &c);
      inline void addType (unsigned offset, const llvm::Type *t);
      inline void growSize (unsigned offset, const llvm::Type *t);
      
      /// unify with a given cell. At the end, both cells point to the
      /// same offset of the same node. Might cause collapse of the
      /// nodes represented by the cells.
      void unify (Cell &c);
      
      void swap (Cell &o)
      { std::swap (m_node, o.m_node); std::swap (m_offset, o.m_offset); }

      /// pretty-printer of a cell
      void write(llvm::raw_ostream&o) const;

      /// for gdb
      void dump () const;
      
    };
    
    
    /// A node of a DSA graph representing a memory object
    class Node 
    {
      friend class Graph;
      friend class Cell;

      friend class FunctionalMapper;
      friend class SimulationMapper;

    public:
      
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

          // XXX: cannot be collapsed and array at the same time
          if (collapsed && array) array = 0;
        }
        void reset () { memset (this, 0, sizeof (*this)); }

        std::string toStr() const 
        {
          std::string flags("");
          if (collapsed) flags += "C";
          if (alloca) flags += "S";
          if (heap) flags += "H";
          if (global) flags += "G";
          if (array) flags += "A";
          if (unknown) flags += "U";
          if (incomplete) flags += "I";
          if (modified) flags += "M";
          if (read) flags += "R";
          if (external) flags += "E";
          if (externFunc) flags += "X";
          if (externGlobal) flags += "Y";
          if (inttoptr) flags += "P";
          if (ptrtoint) flags += "2";
          if (vastart) flags += "V";
          if (dead) flags += "D";
          return flags;
        }
        
      };

     protected:

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

     private:
      
      /// parent DSA graph
      Graph *m_graph;
      /// node marks
      struct NodeType m_nodeType;
      mutable const llvm::Value *m_unique_scalar;
      bool m_has_unique_scalar;
      /// When the node is forwarding, the memory cell at which the
      /// node begins in some other memory object
      Cell m_forward;
      
    public:

      typedef Graph::Set Set;
      typedef boost::container::flat_map<unsigned,  Set> types_type;      
      typedef boost::container::flat_map<unsigned, CellRef> links_type;

      // Iterator for graph interface... Defined in GraphTraits.h
      typedef NodeIterator<Node> iterator;
      typedef NodeIterator<const Node> const_iterator;
      iterator begin();
      iterator end();
      const_iterator begin() const;
      const_iterator end() const;

      NodeType getNodeType () const {
	return m_nodeType;
      }
      
    private:
      
      /// known type of every offset/field
      types_type m_types;
      /// destination of every offset/field
      links_type m_links;
      
      /// known size
      unsigned m_size;

      /// allocation sites for the node
      typedef boost::container::flat_set<const llvm::Value*> AllocaSet;
      AllocaSet m_alloca_sites;

      static uint64_t m_id_factory;

      uint64_t m_id; // global id for the node

      Node (Graph &g) : m_graph (&g), m_unique_scalar (nullptr), 
                        m_has_unique_scalar (false), m_size (0), m_id (++m_id_factory){}

      Node (Graph &g, const Node &n, bool copyLinks = false);
      
      void compress ()
      {
        m_types.shrink_to_fit ();
        m_links.shrink_to_fit ();
        m_alloca_sites.shrink_to_fit ();
      }
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
        auto &res = m_links [offset];
        if (!res) res.reset (new Cell ());
        return *res;
      }
      
      /// Adds a set of types for a field at a given offset
      void addType (const Offset &offset, Set types);
      
      /// joins all the types of a given node starting at a given
      /// offset of the current node
      void joinTypes (unsigned offset, const Node &n);
      
      /// increase size to accommodate a field of type t at the given offset
      void growSize (const Offset &offset, const llvm::Type *t);
      Node &setArray (bool v = true) { m_nodeType.array = v; return *this; }

      void writeTypes (llvm::raw_ostream &o) const;

    public:

      /// delete copy constructor
      Node (const Node &n) = delete;
      /// delete assignment
      Node &operator=(const Node &n) = delete;
      
      /// unify with a given node
      void unify (Node &n) { unifyAt (n, 0); }

      Node &setAlloca (bool v = true) { m_nodeType.alloca = v; return *this;}
      Node &setHeap (bool v = true) { m_nodeType.heap = v; return *this;}
      Node &setRead (bool v = true) { m_nodeType.read = v; return *this;}
      Node &setModified (bool v = true) { m_nodeType.modified = v; return *this;}
      Node &setExternal (bool v = true) { m_nodeType.external = v; return *this;}
      Node &setIntToPtr (bool v = true) { m_nodeType.inttoptr = v; return *this;}
      Node &setPtrToInt (bool v = true) { m_nodeType.ptrtoint = v; return *this;}

      bool isAlloca () const { return m_nodeType.alloca; }
      bool isHeap () const { return m_nodeType.heap; }
      bool isRead () const { return m_nodeType.read; }
      bool isModified () const { return m_nodeType.modified; }
      bool isExternal () const { return m_nodeType.external; }
      bool isIntToPtr () const { return m_nodeType.inttoptr; }
      bool isPtrToInt () const { return m_nodeType.ptrtoint; }

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
      const llvm::Value *getUniqueScalar () const { return m_unique_scalar; }
      void setUniqueScalar (const llvm::Value *v) 
      {m_unique_scalar = v; m_has_unique_scalar=true;}
      bool hasUniqueScalar () const { return m_has_unique_scalar;}
      /// compute a simulation relation between this and n while
      /// propagating unique scalars for all the nodes in the
      /// relation. The result can only be one of these four values:
      /// 0x0 (no change), 0x1 (this changed), 0x2 (n changed), 0x3
      /// (both changed).
      unsigned mergeUniqueScalar (Node &n);
      template<typename Cache>
      unsigned mergeUniqueScalar (Node &n, Cache &seen);      

      inline bool isForwarding () const;
      
      // global id for the node
      uint64_t getId () const { return m_id;}

      Graph *getGraph () { return m_graph; } 
      const Graph *getGraph () const { return m_graph; } 
      
      /// Return a node the current node represents. If the node is
      /// forwarding, returns the non-forwarding node this node points
      /// to. Might be expensive.
      inline Node* getNode ();
      inline const Node* getNode () const;
      unsigned getRawOffset () const;

      types_type &types () { return m_types; }
      const types_type &types () const { return m_types; }
      links_type &links () { return m_links; }
      const links_type &links () const { return m_links; }

      unsigned size () const { return m_size; }
      void growSize (unsigned v);
      

      bool hasLink (unsigned offset) const
      { return m_links.count (Offset (*this, offset)) > 0; }
      const Cell &getLink (unsigned offset) const
      {return *m_links.at (Offset (*this, offset));}
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
      /// tag argument is used for debugging only
      void collapse (int tag /*= -2*/);

      /// Add a new allocation site
      void addAllocSite (const llvm::Value &v);
      /// get all allocation sites
      const AllocaSet& getAllocSites () const { return m_alloca_sites;}
      /// joins all the allocation sites
      void joinAllocSites (const AllocaSet& s);
      /// compute a simulation relation between this and n while
      /// propagating allocation sites for all the nodes in the
      /// relation. The result can only be one of these four values:
      /// 0x0 (no change), 0x1 (this changed), 0x2 (n changed), 0x3
      /// (both changed).
      unsigned mergeAllocSites (Node &n);
      template<typename Cache>
      unsigned mergeAllocSites (Node &n, Cache &seen);      
      
      /// pretty-printer of a node
      void write(llvm::raw_ostream&o) const;    

      /// for gdb
      void dump () const;
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

    void Cell::growSize (unsigned o, const llvm::Type *t)
    {
      assert (!isNull ());
      Node::Offset offset (*getNode (), m_offset + o);
      getNode ()->growSize (offset, t);
    }
      
    
    
    Node* Node::getNode () 
    { return isForwarding () ? m_forward.getNode () : this;}

    const Node* Node::getNode () const
    { return isForwarding () ? m_forward.getNode () : this;}
  }  

}

namespace llvm
{
    inline raw_ostream& operator<<(raw_ostream& o, const seahorn::dsa::Node &n) 
    { n.write(o); return o; }
    inline raw_ostream& operator<<(raw_ostream& o, const seahorn::dsa::Cell &c)
    { c.write(o); return o; }
}

namespace std
{
  template<> struct hash<seahorn::dsa::Cell>
  {
    size_t operator() (const seahorn::dsa::Cell &c) const
    {
      size_t seed = 0;
      boost::hash_combine (seed, c.getNode ());
      boost::hash_combine (seed, c.getRawOffset ());
      return seed;
    }
  };
}

#endif
