#ifndef __DSA_GRAPH_TRAITS_H
#define __DSA_GRAPH_TRAITS_H

#include "seahorn/Analysis/DSA/Graph.hh"
#include "llvm/ADT/GraphTraits.h"
#include "llvm/ADT/STLExtras.h"

#include <iterator>

namespace seahorn {

  namespace dsa {
    
    template<typename NodeTy>
    class NodeIterator :
      public std::iterator <std::forward_iterator_tag, /*const*/ Node> {

      friend class Node;
      
      typename Node::links_type::const_iterator _links_it;
      
      typedef NodeIterator<NodeTy> this_type;
      
      NodeIterator(NodeTy *N) : _links_it(N->links().begin()) {}   // begin iterator
      NodeIterator(NodeTy *N, bool) : _links_it(N->links().end()) {}  // Create end iterator
    
    public:
      
      bool operator==(const this_type& x) const {
	return _links_it == x._links_it;
      }
      
      bool operator!=(const this_type& x) const { return !operator==(x); }
      
      const this_type &operator=(const this_type &o) {
	_links_it = o._links_it;
	return *this;
      }
      
      pointer operator*() const {
	return _links_it->second->getNode();
      }
      
      pointer operator->() const { return operator*(); }
      
      this_type& operator++() {                // Preincrement
	++_links_it;
	return *this;
      }
      
      this_type operator++(int) { // Postincrement
	this_type tmp = *this; ++*this; return tmp;
      }
      
      unsigned getOffset() const { return _links_it->first; }
    };

    
    // Provide iterators for Node...
    Node::iterator Node::begin() { return Node::iterator(this); }
    
    Node::iterator Node::end() { return Node::iterator(this, false); }

    Node::const_iterator Node::begin() const { return Node::const_iterator(this); }
    
    Node::const_iterator Node::end() const { return Node::const_iterator(this, false); }
    
  } // end namespace dsa 
} // end namespace seahorn 

namespace llvm {
  
  template <> struct GraphTraits<seahorn::dsa::Node*> {
    typedef seahorn::dsa::Node NodeType;
    typedef seahorn::dsa::Node::iterator ChildIteratorType;
    
    static NodeType *getEntryNode(NodeType *N) { return N; }
    static ChildIteratorType child_begin(NodeType *N) { return N->begin(); }
    static ChildIteratorType child_end(NodeType *N) { return N->end(); }
  };

  template <> struct GraphTraits<const seahorn::dsa::Node*> {
    typedef const seahorn::dsa::Node NodeType;
    typedef seahorn::dsa::Node::const_iterator ChildIteratorType;
    
    static NodeType *getEntryNode(NodeType *N) { return N; }
    static ChildIteratorType child_begin(NodeType *N) { return N->begin(); }
    static ChildIteratorType child_end(NodeType *N) { return N->end(); }
  };

  template <> struct GraphTraits<seahorn::dsa::Graph*> {
    typedef seahorn::dsa::Node NodeType;
    typedef seahorn::dsa::Node::iterator ChildIteratorType;
    
    // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
    typedef seahorn::dsa::Graph::iterator nodes_iterator;
    
    static nodes_iterator nodes_begin(seahorn::dsa::Graph *G) { return G->begin(); }
    static nodes_iterator nodes_end(seahorn::dsa::Graph *G) { return G->end(); }
    
    static ChildIteratorType child_begin(NodeType *N) { return N->begin(); }
    static ChildIteratorType child_end(NodeType *N) { return N->end(); }
  };

  template <> struct GraphTraits<const seahorn::dsa::Graph*> {
    typedef const seahorn::dsa::Node NodeType;
    typedef seahorn::dsa::Node::const_iterator ChildIteratorType;
    
    // nodes_iterator/begin/end - Allow iteration over all nodes in the graph
    typedef seahorn::dsa::Graph::const_iterator nodes_iterator;
    
    static nodes_iterator nodes_begin(const seahorn::dsa::Graph *G) { return G->begin(); }
    static nodes_iterator nodes_end(const seahorn::dsa::Graph *G) { return G->end(); }
    
    static ChildIteratorType child_begin(NodeType *N) { return N->begin(); }
    static ChildIteratorType child_end(NodeType *N) { return N->end(); }
  };
  
} // End llvm namespace

#endif
