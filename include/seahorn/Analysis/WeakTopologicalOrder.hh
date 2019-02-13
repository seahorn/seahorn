#ifndef __WEAK_TOPOLOGICAL_ORDER__HH_
#define __WEAK_TOPOLOGICAL_ORDER__HH_

#include "llvm/Support/raw_ostream.h"

#include <deque>
#include <memory>
#include <type_traits>
#include <vector>

#include "seahorn/Support/LlvmBgl.hh"

#include "boost/iterator/indirect_iterator.hpp"
#include "boost/iterator/transform_iterator.hpp"
#include "boost/make_shared.hpp"
#include "boost/optional.hpp"
#include "boost/range/iterator_range.hpp"
#include "boost/unordered_map.hpp"
#include <boost/graph/graph_traits.hpp>
#include <boost/graph/properties.hpp>
#include <boost/shared_ptr.hpp>


/*

  Compute the weak topological ordering (WTO) of a directed graph
  based on the paper "Efficient chaotic iteration strategies with
  widenings" by Bourdoncle 1993.

  Some definitions to understand what a WTO is:
   - A hierarchical order of a set is a well-parenthesized permutation
     of this set without two consecutives "(".
   - The elements between "(" and ")" are called components.
   - The first element of a component is called head.
   - We call \omega(c) the set of heads of the (nested) components containing c
   - A weak topological ordering (WTO) of a directed graph is a
        hierarchical order of its vertices such that for each edge x->y, either:
        a) x appears before y **and** y \notin \omega(x), or
        b) y appears before y **and** y \notin \omega(x)
*/

namespace llvm {
class BasicBlock;
}

namespace seahorn {

namespace wto_impl {
// Here to print the graph vertex label to the ostream
// Must be defined for each kind of graph.
template <typename T> void write_graph_vertex(llvm::raw_ostream &o, T e);
} // namespace wto_impl

template <typename E> class WtoElementVisitor;

// Another C++ datatype ...
// WtoElement = [ WtoSingleton | WtoComponent]
template <typename E> class WtoElement {
public:
  typedef WtoElementVisitor<E> wto_element_visitor_t;

  virtual void accept(wto_element_visitor_t *) = 0;

  virtual void write(llvm::raw_ostream &o) const = 0;

  virtual ~WtoElement() {}
};

template <typename E> class WtoSingleton : public WtoElement<E> {

public:
  typedef WtoElement<E> wto_element_t;
  typedef WtoElementVisitor<E> wto_element_visitor_t;

private:
  E m_singleton;

public:
  WtoSingleton(E e) : m_singleton(e) {}

  E get() const { return m_singleton; }

  void accept(wto_element_visitor_t *v) { v->visit(*this); }

  void write(llvm::raw_ostream &o) const {
    wto_impl::write_graph_vertex(o, m_singleton);
  }
};

template <typename E> class WtoComponent : public WtoElement<E> {

public:
  typedef WtoElementVisitor<E> wto_element_visitor_t;
  typedef WtoElement<E> wto_element_t;
  typedef boost::shared_ptr<wto_element_t> wto_element_ptr;
  typedef std::deque<wto_element_ptr> wto_components_t;

private:
  E m_head;
  wto_components_t m_components;

public:
  typedef boost::indirect_iterator<typename wto_components_t::iterator>
      iterator;
  typedef boost::indirect_iterator<typename wto_components_t::const_iterator>
      const_iterator;

  WtoComponent(E head, wto_components_t components)
      : m_head(head), m_components(components) {}

  iterator begin() {
    return boost::make_indirect_iterator(m_components.begin());
  }

  iterator end() { return boost::make_indirect_iterator(m_components.end()); }

  const_iterator begin() const {
    return boost::make_indirect_iterator(m_components.begin());
  }

  const_iterator end() const {
    return boost::make_indirect_iterator(m_components.end());
  }

  E head() const { return m_head; }

  void accept(wto_element_visitor_t *v) { v->visit(*this); }

  void write(llvm::raw_ostream &o) const {
    o << "(";
    wto_impl::write_graph_vertex(o, m_head);
    if (!m_components.empty()) {
      o << " ";
      for (const_iterator it = begin(), et = end(); it != et;) {
        auto &c = *it;
        c.write(o);
        ++it;
        if (it != et)
          o << " ";
      }
    }
    o << ")";
  }
};

template <typename E> class WtoElementVisitor {

public:
  typedef WtoSingleton<E> wto_singleton_t;
  typedef WtoComponent<E> wto_component_t;

  virtual void visit(const wto_singleton_t &) = 0;

  virtual void visit(const wto_component_t &) = 0;

  virtual ~WtoElementVisitor() {}
};

/// Constructs a weak topological order of a BGL graph
template <typename G> class WeakTopoOrder {

public:
  typedef typename boost::graph_traits<G>::vertex_descriptor vertex_t;

private:
  // A helper class to extend an unsigned number with +oo;
  class Number {

    boost::optional<unsigned> m_n;

  public:
    // +oo
    Number() : m_n(boost::none) {}

    static Number plus_infinite() { return Number(); }

    Number(unsigned n) : m_n(n) {}

    Number(const Number &o) : m_n(o.m_n) {}

    Number &operator=(Number o) {
      m_n = o.m_n;
      return *this;
    }

    bool is_plus_infinite() const { return m_n == boost::none; }

    bool is_finite() const { return !is_plus_infinite(); }

    unsigned number() const {
      assert(is_finite());
      return *m_n;
    }

    bool operator==(Number o) const {
      if (is_plus_infinite() && o.is_plus_infinite())
        return true;

      if (is_plus_infinite() || o.is_plus_infinite())
        return false;

      return (number() == o.number());
    }

    bool operator<=(Number o) const {
      if (is_plus_infinite() && o.is_plus_infinite())
        return true;

      if (is_plus_infinite())
        return false;

      if (o.is_plus_infinite())
        return true;

      return (number() <= o.number());
    }

    void write(llvm::raw_ostream &o) const {
      if (is_plus_infinite())
        o << "+oo";
      else
        o << number();
    }
  };

  typedef WtoElement<vertex_t> wto_element_t;
  typedef WtoSingleton<vertex_t> wto_singleton_t;
  typedef WtoComponent<vertex_t> wto_component_t;

  typedef boost::shared_ptr<wto_element_t> wto_element_ptr;
  typedef std::deque<wto_element_ptr> partition_t;
  typedef boost::unordered_map<vertex_t, Number> dfn_map_t;
  typedef std::vector<vertex_t> stack_t;
  typedef boost::unordered_map<vertex_t, std::vector<wto_component_t>>
      nested_components_t;

  //! the graph
  G *m_g;

  //! internal datastructures to compute the wto
  dfn_map_t m_dfn;
  stack_t m_stack;
  unsigned m_cur_dfn_num;

  //! the resulting wto of the graph
  partition_t m_partition;
  //! map each vertex to its nested components
  nested_components_t m_nested_components;

private:
  // helper to avoid initializing all vertices to zero
  Number getDfn(vertex_t v) const {
    auto it = m_dfn.find(v);
    if (it != m_dfn.end())
      return it->second;
    return 0;
  }

  // as described in Bourdoncle's
  partition_t component(vertex_t v) {
    partition_t partition;
    for (auto vw : boost::make_iterator_range(boost::out_edges(v, *m_g))) {
      auto w = boost::target(vw, *m_g);
      if (getDfn(w) == 0)
        visit(w, partition);
    }
    return partition;
  }

  // as described in Bourdoncle's
  Number visit(vertex_t v, partition_t &partition) {
    m_stack.push_back(v);
    m_dfn[v] = m_cur_dfn_num++;
    auto head = getDfn(v);
    bool loop = false;
    for (auto vw : boost::make_iterator_range(boost::out_edges(v, *m_g))) {
      auto w = boost::target(vw, *m_g);
      auto min = getDfn(w);
      if (min == 0)
        min = visit(w, partition);
      if (min <= head) {
        head = min;
        loop = true;
      }
    }

    if (head == getDfn(v)) { // v is the head of a component
      m_dfn[v] = Number::plus_infinite();
      auto element = m_stack.back();
      m_stack.pop_back();
      if (loop) {
        while (!(element == v)) {
          m_dfn[element] = 0; // reset
          element = m_stack.back();
          m_stack.pop_back();
        }
        partition.push_front(boost::static_pointer_cast<wto_element_t>(
            boost::make_shared<wto_component_t>(v, component(v))));
      } else {
        partition.push_front(boost::static_pointer_cast<wto_element_t>(
            boost::make_shared<wto_singleton_t>(v)));
      }
    }
    return head;
  }

  // This is for building the \omega function from Bourdoncle's paper.
  // \omega(c) is the set of heads of the (nested) components containing c
  template <typename E, typename NestedComponentsTable>
  class NestedComponentsVisitor : public WtoElementVisitor<E> {
    typedef WtoElementVisitor<E> wto_element_visitor_t;
    typedef typename wto_element_visitor_t::wto_singleton_t wto_singleton_t;
    typedef typename wto_element_visitor_t::wto_component_t wto_component_t;

    std::vector<wto_component_t> m_nested_components;
    NestedComponentsTable &m_nested_components_table;

  public:
    NestedComponentsVisitor(NestedComponentsTable &t)
        : wto_element_visitor_t(), m_nested_components_table(t) {}

    virtual void visit(const wto_singleton_t &s) {
      m_nested_components_table[s.get()] = m_nested_components;
    }

    virtual void visit(const wto_component_t &c) {
      m_nested_components.push_back(c);
      m_nested_components_table[c.head()] = m_nested_components;
      for (auto &e : c) {
        e.accept(this);
      }
      m_nested_components.pop_back();
    }
  };

  // build a map from graph vertex to nested components in the wto
  void buildNestedComponents() {
    NestedComponentsVisitor<vertex_t, nested_components_t> vis(
        m_nested_components);
    for (auto c : m_partition) {
      c->accept(&vis);
    }
  }

  struct getHead : public std::unary_function<wto_component_t, vertex_t> {
    getHead() {}
    vertex_t operator()(const wto_component_t &c) const { return c.head(); }
  };

public:
  typedef boost::indirect_iterator<typename partition_t::iterator> iterator;
  typedef boost::indirect_iterator<typename partition_t::const_iterator>
      const_iterator;
  typedef boost::transform_iterator<
      getHead, typename std::vector<wto_component_t>::iterator>
      nested_components_iterator;
  typedef boost::transform_iterator<
      getHead, typename std::vector<wto_component_t>::const_iterator>
      nested_components_const_iterator;

  WeakTopoOrder() : m_g(nullptr), m_cur_dfn_num(0) {}

  void buildWto(G *g, vertex_t r) {
    m_g = g;
    visit(r, m_partition);
    buildNestedComponents();
    // cleanup
    m_stack.clear();
    m_dfn.clear();
  }

  void write(llvm::raw_ostream &o) const {
    for (auto &c : boost::make_iterator_range(begin(), end())) {
      c.write(o);
      o << " ";
    }
  }

  iterator begin() {
    return boost::make_indirect_iterator(m_partition.begin());
  }
  iterator end() { return boost::make_indirect_iterator(m_partition.end()); }

  const_iterator begin() const {
    return boost::make_indirect_iterator(m_partition.begin());
  }
  const_iterator end() const {
    return boost::make_indirect_iterator(m_partition.end());
  }

  nested_components_iterator nested_components_begin(vertex_t v) {
    return boost::make_transform_iterator(m_nested_components[v].begin(),
                                          getHead());
  }
  nested_components_iterator nested_components_end(vertex_t v) {
    return boost::make_transform_iterator(m_nested_components[v].end(),
                                          getHead());
  }

  nested_components_const_iterator nested_components_begin(vertex_t v) const {
    auto it = m_nested_components.find(v);
    assert(it != m_nested_components.end());
    return boost::make_transform_iterator(it->second.begin(), getHead());
  }
  nested_components_const_iterator nested_components_end(vertex_t v) const {
    auto it = m_nested_components.find(v);
    assert(it != m_nested_components.end());
    return boost::make_transform_iterator(it->second.end(), getHead());
  }
};
} // namespace seahorn
#endif
