#ifndef __EXPR__H_
#define __EXPR__H_

#pragma clang diagnostic ignored "-Wpotentially-evaluated-expression"

#include "boost/functional/hash_fwd.hpp"
#include <algorithm>
#include <array>
#include <functional>
#include <iomanip>
#include <iostream>
#include <map>
#include <memory>
#include <set>
#include <string>
#include <typeinfo>
#include <unordered_map>
#include <unordered_set>
#include <vector>

#include <gmpxx.h>

/** boost */
#include <boost/interprocess/containers/flat_set.hpp>
#include <boost/intrusive_ptr.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/pool/pool.hpp>
#include <boost/pool/pool_alloc.hpp>
#include <boost/pool/poolfwd.hpp>
#include <boost/ptr_container/ptr_vector.hpp>
#include <boost/range/adaptor/reversed.hpp>
#include <boost/range/iterator_range.hpp>
#include <boost/utility.hpp>

#define mk_it_range boost::make_iterator_range

#define NOP_BASE(NAME)                                                         \
  struct NAME : public expr::Operator {};

#define NOP(NAME, TEXT, STYLE, BASE)                                           \
  struct __##NAME {                                                            \
    static inline std::string name() { return TEXT; }                          \
  };                                                                           \
  typedef DefOp<__##NAME, BASE, STYLE> NAME;

namespace expr {
/* create a namespace op */
namespace op {}

using namespace expr::op;

class ENode;
class ExprFactory;
class ExprFactoryAllocator;

typedef boost::intrusive_ptr<ENode> Expr;
typedef std::set<Expr> ExprSet;
typedef std::vector<Expr> ExprVector;
typedef std::pair<Expr, Expr> ExprPair;
typedef std::map<Expr, Expr> ExprMap;

/* Helper functions to convert from different wrappers over
   expressions into a pointer to an expression node */
inline ENode *eptr(ENode *p) { return p; }
inline const ENode *eptr(const ENode *p) { return p; }
inline ENode *eptr(ENode &p) { return &p; }
inline const ENode *eptr(const ENode &p) { return &p; }
inline ENode *eptr(const Expr &e) { return e.get(); }
inline ENode *eptr(Expr &e) { return e.get(); }
// inline ENode* eptr (Expr e) { return e.get (); }

class Operator;

/* An operator (a.k.a. a tag) of an expression node */
class Operator {
public:
  virtual ~Operator(){};

  /** Print an expression rooted at the operator
      OS    -- the output strream
      args  -- the arguments of the operator
      depth -- indentation level for any new line
      brkt  -- whether the context in which the operator is printed
            -- might be ambiguous and brakets might be required
   **/
  virtual void Print(std::ostream &OS, const std::vector<ENode *> &args,
                     int depth = 0, bool brkt = true) const = 0;
  virtual bool operator==(const Operator &rhs) const = 0;
  virtual bool operator<(const Operator &rhs) const = 0;
  virtual size_t hash() const = 0;
  virtual bool isMutable() const { return false; }
  /* Returns a heap-allocated clone of this */
  virtual Operator *clone(ExprFactoryAllocator &allocator) const = 0;
};

inline std::ostream &operator<<(std::ostream &OS, const Operator &V) {
  std::vector<ENode *> x;
  V.Print(OS, x);
  return OS;
}

/* An expression node (a.k.a. an enode). A pointer into an
   expression tree (or DAG)  */
class ENode {
private:
  // // -- no default constructor
  ENode() : id(0), count(0), fac(NULL) {}
  // // -- no copy constructor
  ENode(const ENode &) : count(0), fac(NULL) {}

protected:
  /** unique identifier of this expression node */
  unsigned int id;
  /** reference counter */
  unsigned int count;

  ExprFactory *fac;
  std::vector<ENode *> args;

  std::shared_ptr<Operator> oper;

  void Deref() {
    if (count > 0)
      count--;
  }

  /** assigns a unique id to the node */
  void setId(unsigned int v) { id = v; }

public:
  ENode(ExprFactory &f, const Operator &o);
  ~ENode();

  ExprFactory &getFactory() const { return *fac; }
  ExprFactory &efac() const { return getFactory(); }

  /** returns the unique id of this expression */
  unsigned int getId() const { return id; }

  void Ref() { count++; }
  bool isGarbage() const { return count == 0; }
  bool isMutable() const { return oper->isMutable(); }

  unsigned int use_count() { return count; }

  ENode *operator[](size_t p) { return arg(p); }
  ENode *arg(size_t p) { return args[p]; }

  ENode *left() { return (args.size() > 0) ? args[0] : NULL; }

  ENode *right() { return (args.size() > 1) ? args[1] : NULL; }

  ENode *first() { return left(); }
  ENode *last() { return args.size() > 0 ? args[args.size() - 1] : NULL; }

  typedef std::vector<ENode *>::const_iterator args_iterator;

  bool args_empty() const { return args.empty(); }
  args_iterator args_begin() const { return args.begin(); }
  args_iterator args_end() const { return args.end(); }

  template <typename iterator> void renew_args(iterator b, iterator e);

  void push_back(ENode *a) {
    args.push_back(a);
    a->Ref();
  }

  size_t arity() const { return args.size(); }

  const Operator &op() const { return *oper; }
  void Print(std::ostream &OS, int depth = 0, bool brkt = true) const {
    oper->Print(OS, args, depth, brkt);
  }
  void dump() const {
    Print(std::cerr, 0, false);
    std::cerr << std::endl;
  }

  friend struct LessENode;
  friend class ExprFactory;
  friend struct std::less<expr::ENode *>;
};

inline std::ostream &operator<<(std::ostream &OS, const ENode &V) {
  V.Print(OS);
  return OS;
}
inline std::ostream &operator<<(std::ostream &OS, const ENode *v) {
  if (v == NULL)
    OS << "NULL";
  else
    OS << *v;
  return OS;
}

struct ENodeUniqueHash {
  std::size_t operator()(const ENode *e) const {
    size_t res = e->op().hash();

    size_t a = e->arity();
    if (a == 0)
      return res;

    ENode::args_iterator it = e->args_begin();
    if (a >= 1)
      boost::hash_combine(res, *it);

    if (a >= 2)
      boost::hash_combine(res, boost::hash_range(it, e->args_end()));

    return res;

    // if (a == 2)
    // 	{
    // 	  boost::hash_combine (res, *it);
    // 	  ++it;
    // 	  boost::hash_combine (res, *it);
    // 	  return res;
    // 	}
    // if (a == 3)
    // 	{
    // 	  boost::hash_combine (res, *it);
    // 	  it++;
    // 	  boost::hash_combine (res, *it);
    // 	  it++;
    // 	  boost::hash_combine (res, *it);
    // 	  return res;
    // 	}

    // // -- n-arry with more than 3 children
    // boost::hash_combine (res,
    // 			   boost::hash_range (e->args_begin (),
    // 					      e->args_end ()));
    // return res;
  }
};

struct ENodeUniqueEqual {
  bool operator()(ENode *const &e1, ENode *const &e2) const {
    // -- same type
    if (typeid(e1->op()) == typeid(e2->op()))
      // -- same number of children
      if (e1->arity() == e2->arity())
        // -- operators (if have data) are equal
        if (e1->op() == e2->op())
          // -- children are equal as pointers
          return std::equal(e1->args_begin(), e1->args_end(), e2->args_begin());
    return false;
  }
};

struct LessENode {
  bool operator()(ENode *e1, ENode *e2) {
    if (typeid(e1->op()) == typeid(e2->op())) {
      if (e1->op() == e2->op())
        return lexicographical_compare(e1->args_begin(), e1->args_end(),
                                       e2->args_begin(), e2->args_end());
      else
        return e1->op() < e2->op();
    }

    // -- when all fails, order by type
    return typeid(e1->op()).before(typeid(e2->op()));
  }
};

/**
 * A type erasure of a cache
 */
struct CacheStub {
  /** true if the stub own the cahce pointer by p */
  virtual bool owns(const void *p) = 0;
  /** erases val from the underlying cache */
  virtual void erase(ENode *val) = 0;
  virtual ~CacheStub() {}
};

template <typename C> struct CacheStubTmpl : CacheStub {
  C &cache;

  CacheStubTmpl(C &c) : cache(c){};

  virtual bool owns(const void *p) {
    return p == static_cast<const void *>(&cache);
  }
  virtual void erase(ENode *val) { cache.erase(val); }
};

struct EFADeleter {
  ExprFactoryAllocator &m_efa;
  EFADeleter(ExprFactoryAllocator &efa) : m_efa(efa) {}
  void operator()(void *p);
};

class ExprFactoryAllocator : boost::noncopyable {
private:
  /** pool for tiny objects */
  boost::pool<> tiny;
  /** pool for small objects */
  boost::pool<> small;

public:
  ExprFactoryAllocator() : tiny(8, 65536), small(64, 65536){};

  void *allocate(size_t n);
  void free(void *block);

  EFADeleter get_deleter();
};

class ExprFactory : boost::noncopyable {
protected:
#define UNORDERED_SET_UNIQUE_TABLE 1
#ifndef UNORDERED_SET_UNIQUE_TABLE
  // -- type of unique table entry
  typedef std::set<ENode *, LessENode> unique_entry_type;
#else
  typedef std::unordered_set<ENode *, ENodeUniqueHash, ENodeUniqueEqual>
      unique_entry_type;
#endif
  typedef const char *unique_key_type;
  // -- type of the unique table
  typedef std::map<unique_key_type, unique_entry_type> unique_type;

  typedef boost::ptr_vector<CacheStub> caches_type;

  /** pool allocator */
  ExprFactoryAllocator allocator;

  /** list of registered caches */
  caches_type caches;

  // -- unique table
  unique_type unique;

  /** counter for assigning unique ids*/
  unsigned int idCount;

  /** returns a unique id > 0 */
  unsigned int uniqueId() { return ++idCount; }

  /**
   * Remove value from unique table
   */
  void Remove(ENode *val) {
    clearCaches(val);
    if (!val->isMutable()) {
      unique_type::iterator it = unique.find(typeid(val->op()).name());
      // -- can only remove things that have been inserted before
      assert(it != unique.end());
      it->second.erase(val);
      if (it->second.empty())
        unique.erase(it);
    }

    freeNode(val);
  }

  /**
   * Clear val from all registered caches
   */
  void clearCaches(ENode *val) {
    for (CacheStub &c : caches)
      c.erase(val);
  }

  /**
   * Return the canonical (unique) representetive of the input
   */
  ENode *canonize(ENode *v) {
    if (v->isMutable()) {
      v->setId(uniqueId());
      return v;
    }

    std::pair<unique_entry_type::iterator, bool> x =
        unique[typeid(v->op()).name()].insert(v);
    if (x.second) {
      v->setId(uniqueId());
      return v;
    } else {
      freeNode(v);
      return *x.first;
    }
  }

  ENode *mkExpr(const Operator &op) { return canonize(allocNode(op)); }

  template <typename etype> ENode *mkExpr(const Operator &op, etype e) {
    ENode *eVal = allocNode(op);
    eVal->push_back(eptr(e));
    return canonize(eVal);
  }

  /** binary */
  template <typename etype>
  ENode *mkExpr(const Operator &op, etype e1, etype e2) {
    ENode *eVal = allocNode(op);
    eVal->push_back(eptr(e1));
    eVal->push_back(eptr(e2));
    return canonize(eVal);
  }

  /** ternary */
  template <typename etype>
  ENode *mkExpr(const Operator &op, etype e1, etype e2, etype e3) {
    ENode *eVal = allocNode(op);
    eVal->push_back(eptr(e1));
    eVal->push_back(eptr(e2));
    eVal->push_back(eptr(e3));
    return canonize(eVal);
  }

  /* n-ary
     iterator ranges over cost ENode*
  */
  template <typename iterator>
  ENode *mkNExpr(const Operator &op, iterator begin, iterator end) {
    ENode *eVal = allocNode(op);
    for (; begin != end; ++begin)
      eVal->push_back(eptr(*begin));
    return canonize(eVal);
  }

private:
#define FREE_LIST_MAX_SIZE 1024 * 4
  std::vector<ENode *> freeList;
  void freeNode(ENode *n);
  ENode *allocNode(const Operator &op);

public:
  ExprFactory() : idCount(0) {}

  /** Derefernce a value */
  void Deref(ENode *val) {
    val->Deref();
    if (val->isGarbage())
      Remove(val);
  }

  /** User functions */
  Expr mkTerm(const Operator &o) { return Expr(mkExpr(o)); }
  Expr mkUnary(const Operator &o, Expr e) { return Expr(mkExpr(o, e.get())); }
  Expr mkBin(const Operator &o, Expr e1, Expr e2) {
    return Expr(mkExpr(o, e1.get(), e2.get()));
  }
  Expr mkTern(const Operator &o, Expr e1, Expr e2, Expr e3) {
    return Expr(mkExpr(o, e1.get(), e2.get(), e3.get()));
  }
  template <typename iterator>
  Expr mkNary(const Operator &o, iterator b, iterator e) {
    return Expr(mkNExpr(o, b, e));
  }

  template <typename Range> Expr mkNary(const Operator &o, const Range &r) {
    return mkNary(o, begin(r), end(r));
  }

  template <typename Cache> void registerCache(Cache &cache) {
    // -- to avoid double registration
    unregisterCache(cache);
    caches.push_back(static_cast<CacheStub *>(new CacheStubTmpl<Cache>(cache)));
  }

  template <typename Cache> bool unregisterCache(const Cache &cache) {
    const void *ptr = static_cast<const void *>(&cache);

    for (caches_type::iterator it = caches.begin(), end = caches.end();
         it != end; ++it)
      if (it->owns(ptr)) {
        caches.erase(it);
        return true;
      }
    return false;
  }

  friend class ENode;
};

inline ENode::ENode(ExprFactory &f, const Operator &o)
    : count(0), fac(&f), oper(o.clone(f.allocator), f.allocator.get_deleter(),
                              boost::pool_allocator<char>()) {}
} // namespace expr

inline void *operator new(size_t n, expr::ExprFactoryAllocator &alloc) {
  return alloc.allocate(n);
}

inline void operator delete(void *p, expr::ExprFactoryAllocator &alloc) {
  alloc.free(p);
}

namespace expr {
inline void ExprFactory::freeNode(ENode *n) {
  if (freeList.size() < FREE_LIST_MAX_SIZE) {
    for (ENode *a : n->args)
      Deref(a);
    n->args.clear();
    n->oper.reset();

    if (freeList.size() < FREE_LIST_MAX_SIZE) {
      assert(n->count == 0);
      freeList.push_back(n);
      return;
    }
  }

  operator delete(static_cast<void *>(n), allocator);
}

inline ENode *ExprFactory::allocNode(const Operator &op) {
  if (freeList.empty())
    return new (allocator) ENode(*this, op);

  ENode *res = freeList.back();
  freeList.pop_back();
  res->oper.reset(op.clone(allocator), allocator.get_deleter(),
                  boost::pool_allocator<char>());
  assert(res->count == 0);
  return res;
}

inline void *ExprFactoryAllocator::allocate(size_t n) {
  if (n <= tiny.get_requested_size())
    return tiny.malloc();
  else if (n <= small.get_requested_size())
    return small.malloc();

  return static_cast<void *>(new char[n]);
}

inline void ExprFactoryAllocator::free(void *block) {
  if (tiny.is_from(block))
    tiny.free(block);
  else if (small.is_from(block))
    small.free(block);
  else
    delete[] static_cast<char *const>(block);
}

inline EFADeleter ExprFactoryAllocator::get_deleter() {
  return EFADeleter(*this);
}

inline void EFADeleter::operator()(void *p) { operator delete(p, m_efa); }

template <typename T> struct TerminalTrait {};

template <typename T, typename P = TerminalTrait<T>>
class Terminal : public Operator {
protected:
  T val;

public:
  typedef T base_type;
  typedef P terminal_type;
  typedef Terminal<T, P> this_type;

  Terminal(const base_type &v) : val(v) {}

  base_type get() const { return val; }

  this_type *clone(ExprFactoryAllocator &allocator) const {
    return new (allocator) this_type(val);
  }

  void Print(std::ostream &OS, const std::vector<ENode *> &args, int depth = 0,
             bool brkt = true) const {
    terminal_type::print(OS, val, depth, brkt);
  }

  bool operator==(const this_type &rhs) const {
    return terminal_type::equal_to(val, rhs.val);
  }

  bool operator<(const this_type &rhs) const {
    return terminal_type::less(val, rhs.val);
  }

  bool operator==(const Operator &rhs) const {
    if (&rhs == this)
      return true;

    const this_type *prhs = dynamic_cast<const this_type *>(&rhs);
    if (prhs == NULL)
      return false;
    return terminal_type::equal_to(val, prhs->val);
  }

  bool operator<(const Operator &rhs) const {
    // x < x is false
    if (&rhs == this)
      return false;

    const this_type *prhs = dynamic_cast<const this_type *>(&rhs);

    return (prhs == NULL) ? typeid(this_type).before(typeid(rhs))
                          : terminal_type::less(val, prhs->val);
  }

  size_t hash() const { return terminal_type::hash(val); }
};

template <> struct TerminalTrait<std::string> {
  static inline void print(std::ostream &OS, const std::string &s, int depth,
                           bool brkt) {
    OS << s;
  }
  static inline bool less(const std::string &s1, const std::string &s2) {
    return s1 < s2;
  }
  static inline bool equal_to(const std::string &s1, const std::string &s2) {
    return s1 == s2;
  }
  static inline size_t hash(const std::string &s) {
    std::hash<std::string> hasher;
    return hasher(s);
  }
};

template <> struct TerminalTrait<int> {
  static inline void print(std::ostream &OS, int s, int depth, bool brkt) {
    OS << s;
  }
  static inline bool less(const int &i1, const int &i2) { return i1 < i2; }
  static inline bool equal_to(int i1, int i2) { return i1 == i2; }
  static inline size_t hash(int i) {
    std::hash<int> hasher;
    return hasher(i);
  }
};

template <> struct TerminalTrait<unsigned int> {
  static inline void print(std::ostream &OS, unsigned int s, int depth,
                           bool brkt) {
    OS << s;
  }
  static inline bool less(const unsigned int &i1, const unsigned int &i2) {
    return i1 < i2;
  }
  static inline bool equal_to(unsigned int i1, unsigned int i2) {
    return i1 == i2;
  }
  static inline size_t hash(unsigned int i) {
    std::hash<unsigned int> hasher;
    return hasher(i);
  }
};

template <> struct TerminalTrait<unsigned long> {
  static inline void print(std::ostream &OS, unsigned long s, int depth,
                           bool brkt) {
    OS << s;
  }
  static inline bool less(const unsigned long &i1, const unsigned long &i2) {
    return i1 < i2;
  }
  static inline bool equal_to(unsigned long l1, unsigned long l2) {
    return l1 == l2;
  }
  static inline size_t hash(unsigned long i) {
    std::hash<unsigned long> hasher;
    return hasher(i);
  }
};

template <> struct TerminalTrait<mpz_class> {
  static inline void print(std::ostream &OS, const mpz_class &v, int depth,
                           bool brkt) {
    /* print large numbers in hex */
    if (v >= 65535 || v <= -65535)
      OS << std::hex << std::showbase;

    OS << v;

    OS << std::dec << std::noshowbase;
  }

  static inline bool less(const mpz_class &v1, const mpz_class &v2) {
    return v1 < v2;
  }

  static inline bool equal_to(const mpz_class &v1, const mpz_class &v2) {
    return v1 == v2;
  }

  static inline size_t hash(const mpz_class &v) {
    std::string str = boost::lexical_cast<std::string>(v);
    std::hash<std::string> hasher;
    return hasher(str);
  }
};

template <> struct TerminalTrait<mpq_class> {
  static inline void print(std::ostream &OS, const mpq_class &v, int depth,
                           bool brkt) {
    OS << v;
  }

  static inline bool less(const mpq_class &v1, const mpq_class &v2) {
    return v1 < v2;
  }

  static inline bool equal_to(const mpq_class &v1, const mpq_class &v2) {
    return v1 == v2;
  }

  static inline size_t hash(const mpq_class &v) {
    std::string str = boost::lexical_cast<std::string>(v);
    std::hash<std::string> hasher;
    return hasher(str);
  }
};

namespace op {
typedef Terminal<std::string> STRING;
typedef Terminal<int> INT;
typedef Terminal<unsigned int> UINT;
typedef Terminal<unsigned long> ULONG;

typedef Terminal<mpq_class> MPQ;
typedef Terminal<mpz_class> MPZ;
} // namespace op

namespace ps {
inline std::ostream &space(std::ostream &OS, size_t c) {
  for (size_t i = 0; i < c; i++)
    OS << " ";
  return OS;
}

struct PREFIX {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    if (args.size() >= 2)
      OS << "[";
    if (args.size() == 1 && brkt)
      OS << "(";

    OS << name;
    if (args.empty())
      return;

    if (args.size() == 1) {
      // OS << " ";
      args[0]->Print(OS, depth + 2, true);
      if (brkt)
        OS << ")";
      return;
    }

    for (std::vector<ENode *>::const_iterator it = args.begin(),
                                              end = args.end();
         it != end; ++it) {
      OS << "\n";
      space(OS, depth + 2);
      (*it)->Print(OS, depth + 2, false);
    }

    OS << "\n";
    space(OS, depth);
    OS << "]";
  }
};

struct INFIX {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {

    if (args.size() != 2) {
      PREFIX::print(OS, depth, brkt, name, args);
      return;
    }

    if (brkt)
      OS << "(";
    args[0]->Print(OS, depth, true);
    OS << name;
    args[1]->Print(OS, depth, true);
    if (brkt)
      OS << ")";
  }
};

struct FUNCTIONAL {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << name << "(";

    bool first = true;
    for (std::vector<ENode *>::const_iterator it = args.begin(),
                                              end = args.end();
         it != end; ++it) {
      if (!first)
        OS << ", ";
      (*it)->Print(OS, depth + 2, false);
      first = false;
    }

    OS << ")";
  }
};

struct LISP {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "(" << name << " ";

    bool first = true;
    for (std::vector<ENode *>::const_iterator it = args.begin(),
                                              end = args.end();
         it != end; ++it) {
      if (!first)
        OS << " ";
      (*it)->Print(OS, depth + 2, true);
      first = false;
    }

    OS << ")";
  }
};
} // namespace ps
using namespace ps;

// compare two operators based on their address
template <typename T> inline bool addrLT(const T &lhs, const Operator *rhs) {
  if (rhs == NULL || lhs == *rhs)
    return false;

  const T *prhs = dynamic_cast<const T *>(rhs);

  if (prhs == NULL)
    return typeid(T).before(typeid(*rhs));

  return &lhs < rhs;
}

// compare two operators based on their types
inline bool typeLT(const Operator *lhs, const Operator *rhs) {
  if (lhs == NULL && rhs != NULL)
    return true;
  if (lhs == NULL && rhs == NULL)
    return false;

  if (rhs == NULL || *lhs == *rhs)
    return false;

  if (typeid(*lhs) == typeid(*rhs))
    return false;

  return typeid(*lhs).before(typeid(*rhs));
}

inline size_t typeHash(const Operator *op) {
  if (op == NULL)
    return 0;
  std::hash<void *> hasher;
  return hasher(static_cast<void *>(const_cast<char *>(typeid(*op).name())));
}

template <typename T, typename B, typename P> struct DefOp : public B {
  typedef DefOp<T, B, P> this_type;
  typedef B base_type;
  typedef T op_type;
  typedef P ps_type;

  void Print(std::ostream &OS, const std::vector<ENode *> &args, int depth = 0,
             bool brkt = true) const {
    ps_type::print(OS, depth, brkt, op_type::name(), args);
  }

  bool operator==(const Operator &rhs) const {
    return typeid(*this) == typeid(rhs);
  }

  bool operator<(const Operator &rhs) const { return typeLT(this, &rhs); }

  size_t hash() const { return typeHash(this); }

  this_type *clone(ExprFactoryAllocator &allocator) const {
    return new (allocator) this_type(*this);
  }
};

inline ENode::~ENode() {
  for (args_iterator b = args.begin(), e = args.end(); b != e; ++b)
    efac().Deref(*b);
}

template <typename iterator> void ENode::renew_args(iterator b, iterator e) {
  std::vector<ENode *> old = args;
  args = std::vector<ENode *>();

  // -- increment reference count of all new arguments
  for (; b != e; ++b)
    this->push_back(eptr(*b));

  // -- decrement reference count of all old arguments
  for (args_iterator b = old.begin(), e = old.end(); b != e; ++b)
    efac().Deref(*b);
}

/** Required by boost::intrusive_ptr */
inline void intrusive_ptr_add_ref(ENode *v) { v->Ref(); }

inline void intrusive_ptr_release(ENode *v) { v->efac().Deref(v); }

struct BoolExprFn {
  virtual ~BoolExprFn() {}
  virtual bool apply(Expr e) = 0;
};

struct TrueBoolExprFn : BoolExprFn {
  bool apply(Expr e) { return true; }
};

struct FalseBoolExprFn : BoolExprFn {
  bool apply(Expr e) { return false; }
};

struct IdentityRewriter {
  IdentityRewriter(){};
  Expr operator()(Expr e) { return e; }
};

struct ExprFn {
  virtual ~ExprFn() {}
  virtual Expr apply(Expr e) = 0;
};

namespace {
template <typename T> struct ExprFunctionoid : public ExprFn {
  typedef std::shared_ptr<T> fn_type;

  fn_type fn;

  ExprFunctionoid(T *f) : fn_type(fn) {}
  ExprFunctionoid(fn_type f) : fn(f) {}
  Expr apply(Expr e) { return (*fn)(e); }
};

} // namespace

class VisitAction {
public:
  // skipKids or doKids
  VisitAction(bool kids = false)
      : _skipKids(kids), fn(new ExprFunctionoid<IdentityRewriter>(
                             std::make_shared<IdentityRewriter>())) {}

  // changeTo or doKidsRewrite
  template <typename R>
  VisitAction(Expr e, bool kids = false,
              std::shared_ptr<R> r = std::make_shared<IdentityRewriter>())
      : _skipKids(kids), expr(e), fn(new ExprFunctionoid<R>(r)) {}

  bool isSkipKids() { return _skipKids && expr.get() == NULL; }
  bool isChangeTo() { return _skipKids && expr.get() != NULL; }
  bool isDoKids() { return !_skipKids && expr.get() == NULL; }
  bool isChangeDoKidsRewrite() { return !_skipKids && expr.get() != NULL; }

  Expr rewrite(Expr v) { return fn->apply(v); }

  Expr getExpr() { return expr; }

  static inline VisitAction skipKids() { return VisitAction(true); }
  static inline VisitAction doKids() { return VisitAction(false); }
  static inline VisitAction changeTo(Expr e) {
    return VisitAction(e, true, std::make_shared<IdentityRewriter>());
  }

  static inline VisitAction changeDoKids(Expr e) {
    return VisitAction(e, false, std::make_shared<IdentityRewriter>());
  }

  template <typename R>
  static inline VisitAction changeDoKidsRewrite(Expr e, std::shared_ptr<R> r) {
    return VisitAction(e, false, r);
  }

protected:
  bool _skipKids;
  Expr expr;

private:
  std::shared_ptr<ExprFn> fn;
};

typedef std::unordered_map<ENode *, Expr> DagVisitCache;

template <typename ExprVisitor>
Expr visit(ExprVisitor &v, Expr expr, DagVisitCache &cache) {
  if (!expr)
    return expr;

  if (expr->use_count() > 1) {
    DagVisitCache::const_iterator cit = cache.find(&*expr);
    if (cit != cache.end())
      return cit->second;
  }

  VisitAction va = v(expr);
  Expr res;

  if (va.isSkipKids())
    res = expr;
  else if (va.isChangeTo())
    res = va.getExpr();
  else {
    res = va.isChangeDoKidsRewrite() ? va.getExpr() : expr;
    if (res->arity() > 0) {
      bool changed = false;
      std::vector<Expr> kids;

      for (ENode::args_iterator b = res->args_begin(), e = res->args_end();
           b != e; ++b) {
        Expr k = visit(v, *b, cache);
        kids.push_back(k);
        changed = (changed || k.get() != *b);
      }

      if (changed) {
        if (!res->isMutable())
          res = res->getFactory().mkNary(res->op(), kids.begin(), kids.end());
        else
          res->renew_args(kids.begin(), kids.end());
      }
    }

    res = va.rewrite(res);
  }

  if (expr->use_count() > 1) {
    expr->Ref();
    cache[&*expr] = res;
  }

  return res;
}

inline void clearDagVisitCache(DagVisitCache &cache) {
  for (DagVisitCache::value_type &kv : cache)
    kv.first->efac().Deref(kv.first);
  cache.clear();
}

template <typename ExprVisitor>
struct DagVisit : public std::unary_function<Expr, Expr> {
  ExprVisitor &m_v;
  DagVisitCache m_cache;

  DagVisit(ExprVisitor &v) : m_v(v) {}
  DagVisit(const DagVisit &o) : m_v(o.m_v) {}
  ~DagVisit() { clearDagVisitCache(m_cache); }

  Expr operator()(Expr e) { return visit(m_v, e, m_cache); }
};

template <typename ExprVisitor> Expr dagVisit(ExprVisitor &v, Expr expr) {
  DagVisit<ExprVisitor> dv(v);
  return dv(expr);
}

template <typename ExprVisitor>
void dagVisit(ExprVisitor &v, const ExprVector &vec) {
  DagVisit<ExprVisitor> dv(v);
  for (auto &e : vec) {
    dv(e);
  }
}

template <typename ExprVisitor> Expr visit(ExprVisitor &v, Expr expr) {
  VisitAction va = v(expr);

  if (va.isSkipKids())
    return expr;

  if (va.isChangeTo())
    return va.getExpr();

  Expr res = va.isChangeDoKidsRewrite() ? va.getExpr() : expr;

  if (res->arity() == 0)
    return va.rewrite(res);

  bool changed = false;
  std::vector<Expr> kids;

  for (ENode::args_iterator b = res->args_begin(), e = res->args_end(); b != e;
       ++b) {
    Expr k = visit(v, *b);
    kids.push_back(k);
    changed = (changed || k.get() != *b);
  }

  if (changed) {
    if (!res->isMutable())
      res = res->getFactory().mkNary(res->op(), kids.begin(), kids.end());
    else
      res->renew_args(kids.begin(), kids.end());
  }

  res = va.rewrite(res);

  return res;
}

/**********************************************************************/
/**********************************************************************/
/*                    PUBLIC API                                      */
/**********************************************************************/
/**********************************************************************/

/**********************************************************************/
/* Inspection */
/**********************************************************************/

// -- usage isOp<TYPE>(EXPR) . Returns true if top operator of
// -- expression is a subclass of TYPE.
template <typename O, typename T> bool isOp(T e) {
  const Operator *op = &(eptr(e)->op());
  const O *top = dynamic_cast<const O *>(op);
  return top != NULL;
}

// -- usage isOpX<TYPE>(EXPR) . Returns true if top operator of
// -- expression is of type TYPE.
template <typename O, typename T> bool isOpX(T e) {
  return typeid(eptr(e)->op()) == typeid(O);
}

/**********************************************************************/
/* Creation */
/**********************************************************************/

/* Creates a nullary expression with operator T.
 * Usage: mk<TRUE> (efac)
 */
template <typename T> Expr mk(ExprFactory &f) { return f.mkTerm(T()); }

/* Creates a terminal expression with a given terminal value
 * Usage: mk (5, efac)
 */
template <typename T> Expr mkTerm(T v, ExprFactory &f) {
  Terminal<T> op(v);
  return f.mkTerm(op);
}

template <typename T> T getTerm(Expr e) {
  typedef Terminal<T> term_type;
  return dynamic_cast<const term_type &>(e->op()).get();
}

/* Creates a unary expression with a given operator.
 * Usage: mk<NEG> (exp)
 */
template <typename T> Expr mk(Expr e) { return e->efac().mkUnary(T(), e); }

template <typename T> Expr mk(Expr e1, Expr e2) {
  return e1->efac().mkBin(T(), e1, e2);
}

template <typename T> Expr mk(Expr e1, Expr e2, Expr e3) {
  return e1->efac().mkTern(T(), e1, e2, e3);
}

/**
 * Creates an nary expression with a given operator.
 * The arguments are given as first and last iterators.
 * Usage: mknary<PLUS> (v.begin (), v.end ())
 */
template <typename T, typename iterator>
Expr mknary(iterator bgn, iterator end) {
  if (bgn == end)
    return Expr(nullptr);
  return eptr(*bgn)->efac().mkNary(T(), bgn, end);
}

template <typename T, typename iterator>
Expr mknary(Expr base, iterator bgn, iterator end) {
  if (bgn == end)
    return base;
  if (std::distance(bgn, end) == 1)
    return eptr(*bgn);
  return mknary<T>(bgn, end);
}

/** boost::range versions of mknary */

template <typename T, typename Range> Expr mknary(const Range &r) {
  return mknary<T>(boost::begin(r), boost::end(r));
}

template <typename T, typename Range> Expr mknary(Expr base, const Range &r) {
  return mknary<T>(base, boost::begin(r), boost::end(r));
}

/**********************************************************************/
/* Constructors that accept explicit operators. Only use those if
   the ones above are not applicable.*/
/**********************************************************************/

/* Creates a nullary expression with a given operator.
 * Usage: mk (op, efac)
 */
inline Expr mk(const Operator &op, ExprFactory &f) { return f.mkTerm(op); }

inline Expr mk(const Operator &o, Expr e) { return e->efac().mkUnary(o, e); }

inline Expr mk(const Operator &o, Expr e1, Expr e2) {
  return e1->efac().mkBin(o, e1, e2);
}

inline Expr mk(const Operator &o, Expr e1, Expr e2, Expr e3) {
  return e1->efac().mkTern(o, e1, e2, e3);
}

template <typename iterator>
Expr mknary(const Operator &o, iterator bgn, iterator end) {
  return eptr(*bgn)->efac().mkNary(o, bgn, end);
}

/**********************************************************************/
/* Operators */
/**********************************************************************/

namespace op {
// -- Boolean opearators
NOP_BASE(BoolOp)

/* operator definitions */
NOP(TRUE, "true", PREFIX, BoolOp)
NOP(FALSE, "false", PREFIX, BoolOp)
NOP(AND, "&&", INFIX, BoolOp)
NOP(OR, "||", INFIX, BoolOp)
NOP(XOR, "^", INFIX, BoolOp)
NOP(NEG, "!", PREFIX, BoolOp)
NOP(IMPL, "->", INFIX, BoolOp)
NOP(ITE, "ite", FUNCTIONAL, BoolOp)
NOP(IFF, "<->", INFIX, BoolOp)

namespace boolop {
// -- logical AND. Applies simplifications
inline Expr land(Expr e1, Expr e2) {
  if (e1 == e2)
    return e1;

  if (isOpX<TRUE>(e1))
    return e2;
  if (isOpX<TRUE>(e2))
    return e1;
  if (isOpX<FALSE>(e1) || isOpX<FALSE>(e2))
    return mk<FALSE>(e1->efac());

  return mk<AND>(e1, e2);
}

inline Expr lor(Expr e1, Expr e2) {
  if (isOpX<FALSE>(e1))
    return e2;
  if (isOpX<FALSE>(e2))
    return e1;
  if (isOpX<TRUE>(e1) || isOpX<TRUE>(e2))
    return mk<TRUE>(e1->efac());
  return mk<OR>(e1, e2);
}

inline Expr limp(Expr e1, Expr e2) {
  // TRUE -> x  IS x
  if (isOpX<TRUE>(e1))
    return e2;
  // x -> TRUE  IS TRUE
  if (isOpX<TRUE>(e2))
    return e2;
  // FALSE -> x IS TRUE
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());
  // x -> x IS TRUE
  if (e1 == e2)
    return mk<TRUE>(e1->efac());

  // x -> FALSE is missing since it adds a negation

  return mk<IMPL>(e1, e2);
}

inline Expr lite(Expr c, Expr t, Expr e) {
  if (isOpX<TRUE>(c))
    return t;
  if (isOpX<FALSE>(c))
    return e;
  if (t == e)
    return t;

  return mk<ITE>(c, t, e);
}

inline Expr lneg(Expr e1) {
  if (isOpX<TRUE>(e1))
    return mk<FALSE>(e1->efac());
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());

  if (isOpX<NEG>(e1))
    return e1->left();

  return mk<NEG>(e1);
}

template <typename R> Expr land(const R &r) {
  assert(boost::begin(r) != boost::end(r));

  // -- reduce unary AND to the operand
  if (boost::size(r) == 1)
    return *boost::begin(r);

  // XXX add more logical simplifications
  return mknary<AND>(r);
}

struct CIRCSIZE : public std::unary_function<Expr, VisitAction> {
  unsigned ands;
  unsigned ors;
  unsigned inputs;

  CIRCSIZE() : ands(0), ors(0), inputs(0) {}

  VisitAction operator()(Expr e) {
    if (isOpX<AND>(e))
      ands++;
    else if (isOpX<OR>(e))
      ors++;
    else if (!isOpX<NEG>(e)) {
      inputs++;
      return VisitAction::skipKids();
    }
    return VisitAction::doKids();
  }

  unsigned size() { return ands + ors + inputs; }
};

/// size of an expression in terms of ANDs, ORs, and inputs.
/// NEG is not counted, other BoolOps are treated as inputs.
inline unsigned circSize(Expr e) {
  CIRCSIZE csz;
  dagVisit(csz, e);
  return csz.size();
}
inline unsigned circSize(const ExprVector &vec) {
  CIRCSIZE csz;
  dagVisit(csz, vec);
  return csz.size();
}

/** trivial simplifier for Boolean Operators */
struct TrivialSimplifier : public std::unary_function<Expr, Expr> {
  ExprFactory &efac;

  Expr trueE;
  Expr falseE;

  TrivialSimplifier(const TrivialSimplifier &o)
      : efac(o.efac), trueE(o.trueE), falseE(o.falseE) {}

  TrivialSimplifier(ExprFactory &fac)
      : efac(fac), trueE(mk<TRUE>(efac)), falseE(mk<FALSE>(efac)) {}

  Expr operator()(Expr exp) {
    if (exp == trueE || exp == falseE)
      return exp;

    if (!isOp<BoolOp>(exp))
      return exp;

    if (isOpX<IMPL>(exp)) {
      // TRUE -> x  == x
      if (trueE == exp->left())
        return exp->right();

      // FALSE -> x == TRUE
      if (falseE == exp->left())
        return trueE;

      // x -> TRUE == TRUE
      if (trueE == exp->right())
        return trueE;

      // x -> FALSE == !x
      if (falseE == exp->right())
        return lneg(exp->left());

      return exp;
    }

    if (isOpX<IFF>(exp)) {
      if (exp->left() == exp->right())
        return exp->left();
      if (trueE == exp->left())
        return exp->right();
      if (falseE == exp->left())
        return lneg(exp->right());
      if (trueE == exp->right())
        return exp->left();
      if (falseE == exp->right())
        return lneg(exp->left());

      return exp;
    }

    if (isOpX<NEG>(exp)) {
      // -- !TRUE -> FALSE
      if (trueE == exp->left())
        return falseE;
      // -- !FALSE -> TRUE
      if (falseE == exp->left())
        return trueE;
      // -- ! ! x -> x
      if (isOpX<NEG>(exp->left()))
        return exp->left()->left();
      return exp;
    }

    int arity = exp->arity();
    if (isOpX<OR>(exp)) {
      if (arity == 0)
        return falseE;
      if (arity == 1)
        return exp->left();
      if (arity == 2) {
        ENode *lhs = exp->left();
        ENode *rhs = exp->right();

        if (lhs == rhs)
          return lhs;
        if (trueE == lhs || trueE == rhs)
          return trueE;
        if (falseE == lhs)
          return rhs;
        if (falseE == rhs)
          return lhs;
        // (!a || a)
        if (isOpX<NEG>(lhs) && lhs->left() == rhs)
          return trueE;
        // (a || !a)
        if (isOpX<NEG>(rhs) && rhs->left() == lhs)
          return trueE;

        return exp;
      }

      // -- arity > 2, check if one arguments is true
      for (ENode *arg : mk_it_range(exp->args_begin(), exp->args_end()))
        if (trueE == arg)
          return trueE;
      return exp;
    }

    if (isOpX<AND>(exp)) {
      if (arity == 0)
        return trueE;
      if (arity == 1)
        return exp->left();

      if (exp->arity() == 2) {
        ENode *lhs = exp->left();
        ENode *rhs = exp->right();

        if (lhs == rhs)
          return lhs;
        if (falseE == lhs || falseE == rhs)
          return falseE;
        if (trueE == lhs)
          return rhs;
        if (trueE == rhs)
          return lhs;
        if (isOpX<NEG>(lhs) && lhs->left() == rhs)
          return falseE;
        if (isOpX<NEG>(rhs) && rhs->left() == lhs)
          return falseE;

        return exp;
      }

      // -- arity > 2, check if one arguments  is false
      for (ENode *arg : mk_it_range(exp->args_begin(), exp->args_end()))
        if (falseE == arg)
          return falseE;
      return exp;
    }

    return exp;
  }
};

/** Rewriter that gathers Boolean operators into n-ary ones */
struct GatherOps : public std::unary_function<Expr, Expr> {
  Expr trueE;
  Expr falseE;

  GatherOps() : trueE(0), falseE(0) {}

  GatherOps(const GatherOps &o) : trueE(o.trueE), falseE(o.falseE) {}

  Expr operator()(Expr exp) {
    // -- create true/false constants for convinience
    if (trueE == NULL) {
      trueE = mk<TRUE>(exp->efac());
      falseE = mk<FALSE>(exp->efac());
    }

    // -- skip terminals
    if (exp->arity() == 0)
      return exp;
    // if (!isBoolOp<X> (exp)) return exp;
    // -- skip anything that is not AND/OR
    if (!(isOpX<AND>(exp) || isOpX<OR>(exp)))
      return exp;

    const Operator &op = exp->op();
    Expr top;
    Expr bot;
    if (isOpX<AND>(exp)) {
      top = trueE;
      bot = falseE;
    } else {
      top = falseE;
      bot = trueE;
    }

    ExprSet newArgs;
    for (Expr a : mk_it_range(exp->args_begin(), exp->args_end()))
      if (!(op == a->op())) {
        if (a == bot)
          return bot;
        else if (a != top)
          newArgs.insert(a);
      } else /* descend into kids that have the same top-level operator */
        for (Expr ka : mk_it_range(a->args_begin(), a->args_end()))
          if (ka == bot)
            return bot;
          else if (ka != top)
            newArgs.insert(ka);

    if (newArgs.empty())
      return top;
    if (newArgs.size() == 1)
      return *(newArgs.begin());
    return exp->efac().mkNary(op, newArgs.begin(), newArgs.end());
  }
};

/** Rewriter that normalizes AND/OR operators */
struct NormalizeOps : public std::unary_function<Expr, Expr> {
  Expr trueE;
  Expr falseE;

  NormalizeOps() : trueE(0), falseE(0) {}

  NormalizeOps(const NormalizeOps &o) : trueE(o.trueE), falseE(o.falseE) {}

  Expr operator()(Expr exp) {
    // -- create true/false constants for convinience
    if (trueE == NULL) {
      trueE = mk<TRUE>(exp->efac());
      falseE = mk<FALSE>(exp->efac());
    }

    // -- skip anything that is not AND/OR
    if (!(isOpX<AND>(exp) || isOpX<OR>(exp)))
      return exp;
    if (exp->arity() == 1)
      return exp->left();

    const Operator &op = exp->op();
    Expr top, bot;
    if (isOpX<AND>(exp)) {
      top = trueE;
      bot = falseE;
    } else {
      top = falseE;
      bot = trueE;
    }

    if (exp->arity() == 0)
      return top;

    if (exp->arity() == 2) {
      if (isOpX<AND>(exp))
        return land(exp->left(), exp->right());
      else /* isOpX<OR> */
        return lor(exp->left(), exp->right());
    }

    ExprSet newArgs;
    for (Expr a : mk_it_range(exp->args_begin(), exp->args_end()))
      if (!(op == a->op())) {
        if (a == bot)
          return bot;
        else if (a != top)
          newArgs.insert(a);
      } else /* descend into kids that have the same top-level operator */
        for (Expr ka : mk_it_range(a->args_begin(), a->args_end()))
          if (ka == bot)
            return bot;
          else if (ka != top)
            newArgs.insert(ka);

    if (newArgs.empty())
      return top;
    if (newArgs.size() == 1)
      return *(newArgs.begin());

    boost::container::flat_set<Expr> args(newArgs.begin(), newArgs.end());
    Expr res = top;
    for (Expr arg : boost::adaptors::reverse(args))
      res = isOpX<AND>(exp) ? land(arg, res) : lor(arg, res);

    return res;
  }

  Expr land(Expr f, Expr g) {
    /** base cases */
    if (f == trueE)
      return g;
    if (g == trueE)
      return f;
    if (f == falseE || g == falseE)
      return falseE;
    if (f == g)
      return f;
    if (f == boolop::lneg(g) || boolop::lneg(f) == g)
      return falseE;

    // -- both not AND operators. Order in some way
    if (!isOpX<AND>(f) && !isOpX<AND>(g))
      return g < f ? mk<AND>(f, g) : mk<AND>(g, f);

    Expr topf = isOpX<AND>(f) ? f->left() : f;
    Expr topg = isOpX<AND>(g) ? g->left() : g;

    Expr top, restF, restG;
    if (topf < topg || topf == topg) {
      top = topf;
      restF = isOpX<AND>(f) ? f->right() : trueE;
    } else
      restF = f;

    if (topg < topf || topg == topf) {
      top = topg;
      restG = isOpX<AND>(g) ? g->right() : trueE;
    } else
      restG = g;

    return boolop::land(top, land(restF, restG));
  }

  Expr lor(Expr f, Expr g) {
    /** base cases */
    if (f == falseE)
      return g;
    if (g == falseE)
      return f;
    if (f == trueE || g == trueE)
      return trueE;
    if (f == g)
      return f;
    if (f == boolop::lneg(g) || boolop::lneg(f) == g)
      return trueE;

    // -- both not AND operators. Order in some way
    if (!isOpX<OR>(f) && !isOpX<OR>(g))
      return g < f ? mk<OR>(f, g) : mk<OR>(g, f);

    Expr topf = isOpX<OR>(f) ? f->left() : f;
    Expr topg = isOpX<OR>(g) ? g->left() : g;

    Expr top, restF, restG;
    if (topf < topg || topf == topg) {
      top = topf;
      restF = isOpX<OR>(f) ? f->right() : falseE;
    } else
      restF = f;

    if (topg < topf || topg == topf) {
      top = topg;
      restG = isOpX<OR>(g) ? g->right() : falseE;
    } else
      restG = g;

    return boolop::lor(top, lor(restF, restG));
  }
};

/** puts an expression into NNF */
struct NNF : public std::unary_function<Expr, VisitAction> {
  ExprFactory &efac;
  std::shared_ptr<TrivialSimplifier> r;

  NNF(const NNF &o) : efac(o.efac), r(o.r) {}

  NNF(ExprFactory &fac)
      : efac(fac), r(std::make_shared<TrivialSimplifier>(efac)) {}

  VisitAction operator()(Expr exp) {
    if (exp->arity() == 0)
      return VisitAction::skipKids();

    // -- AND / OR -- run the simplifier
    if (isOpX<AND>(exp) || isOpX<OR>(exp))
      return VisitAction::changeDoKidsRewrite(exp, r);

    // -- not a negation, then do not touch, must be non-Boolean
    if (!isOpX<NEG>(exp))
      return VisitAction::skipKids();

    // -- if here, top operator is negation, push it in
    Expr lhs = exp->left();
    if (lhs == r->falseE)
      return VisitAction::changeTo(r->trueE);
    if (lhs == r->trueE)
      return VisitAction::changeTo(r->falseE);

    // -- !!x -- Trivial simplifer will get rid of unary AND
    if (isOpX<NEG>(lhs))
      return VisitAction::changeDoKidsRewrite(mk<AND>(lhs->left()), r);

    // -- ! (x & b) ==> !x || !b
    if (isOpX<OR>(lhs) || isOpX<AND>(lhs)) {
      // -- negate arguments
      ExprVector args;
      for (Expr arg : mk_it_range(lhs->args_begin(), lhs->args_end()))
        args.push_back(lneg(arg));

      // -- flip operator
      Expr res = isOpX<OR>(lhs) ? mknary<AND>(args.begin(), args.end())
                                : mknary<OR>(args.begin(), args.end());
      return VisitAction::changeDoKidsRewrite(res, r);
    }

    // -- negation of anything else, don't descend
    return VisitAction::skipKids();
  }
};

} // namespace boolop

} // namespace op

/// Gates
/// Gates are mutable and are not structurally hashed
namespace op {
struct GateOp : public expr::Operator {
  virtual bool isMutable() const { return true; }
};

/// an output gate
NOP(OUT_G, "OUT_G", PREFIX, GateOp)
NOP(AND_G, "/\\", INFIX, GateOp);
NOP(OR_G, "\\/", INFIX, GateOp);
NOP(NEG_G, "~", PREFIX, GateOp);

namespace gate {
inline Expr land(Expr e1, Expr e2) {
  if (e1 == e2)
    return e1;

  if (isOpX<TRUE>(e1))
    return e2;
  if (isOpX<TRUE>(e2))
    return e1;
  if (isOpX<FALSE>(e1) || isOpX<FALSE>(e2))
    return mk<FALSE>(e1->efac());

  return mk<AND_G>(e1, e2);
}

inline Expr lor(Expr e1, Expr e2) {
  if (isOpX<FALSE>(e1))
    return e2;
  if (isOpX<FALSE>(e2))
    return e1;
  if (isOpX<TRUE>(e1) || isOpX<TRUE>(e2))
    return mk<TRUE>(e1->efac());
  return mk<OR_G>(e1, e2);
}

inline Expr lneg(Expr e1) {
  if (isOpX<TRUE>(e1))
    return mk<FALSE>(e1->efac());
  if (isOpX<FALSE>(e1))
    return mk<TRUE>(e1->efac());

  if (isOpX<NEG_G>(e1) || isOpX<NEG>(e1))
    return e1->left();

  return mk<NEG_G>(e1);
}
} // namespace gate
} // namespace op

namespace op {
// -- Numeric operators
NOP_BASE(NumericOp)

NOP(PLUS, "+", INFIX, NumericOp)
NOP(MINUS, "-", INFIX, NumericOp)
NOP(MULT, "*", INFIX, NumericOp)
NOP(DIV, "/", INFIX, NumericOp)
NOP(IDIV, "/", INFIX, NumericOp);
NOP(MOD, "mod", INFIX, NumericOp)
NOP(REM, "%", INFIX, NumericOp)
NOP(UN_MINUS, "-", PREFIX, NumericOp)
NOP(ABS, "abs", FUNCTIONAL, NumericOp)

NOP(PINFTY, "oo", PREFIX, NumericOp)
NOP(NINFTY, "-oo", PREFIX, NumericOp)

namespace numeric {
struct ITV_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "[";
    args[0]->Print(OS, depth, false);
    OS << ",";
    args[1]->Print(OS, depth, false);
    OS << "]";
  }
};
} // namespace numeric
NOP(ITV, "itv", numeric::ITV_PS, NumericOp)
} // namespace op

namespace op {
// -- Comparisson operators
NOP_BASE(ComparissonOp)

NOP(EQ, "=", INFIX, ComparissonOp)
NOP(NEQ, "!=", INFIX, ComparissonOp)
NOP(LEQ, "<=", INFIX, ComparissonOp)
NOP(GEQ, ">=", INFIX, ComparissonOp)
NOP(LT, "<", INFIX, ComparissonOp)
NOP(GT, ">", INFIX, ComparissonOp)
} // namespace op

namespace op {
// -- Not yet sorted operators
NOP_BASE(MiscOp)

/** A non-deterministic value */
NOP(NONDET, "nondet", FUNCTIONAL, MiscOp)
/** An assumption */
NOP(ASM, "ASM", PREFIX, MiscOp)
/** A tupple */
NOP(TUPLE, "tuple", FUNCTIONAL, MiscOp)
} // namespace op

namespace op {
namespace variant {
struct PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    args[1]->Print(OS, depth, true);
    OS << "_";
    args[0]->Print(OS, depth, true);
  }
};

struct PS_TAG {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    args[1]->Print(OS, depth, true);
    OS << "!";
    args[0]->Print(OS, depth, true);
  }
};
} // namespace variant
NOP_BASE(VariantOp)
NOP(VARIANT, "variant", variant::PS, VariantOp)
NOP(TAG, "tag", variant::PS_TAG, VariantOp)

namespace variant {
/** Creates a variant of an expression. For example,
    `variant (1, e)` creates an expression `e_1`
*/
inline Expr variant(int v, Expr e) {
  return mk<VARIANT>(mkTerm(v, e->efac()), e);
}

inline Expr next(Expr e) { return variant(1, e); }
inline Expr aux(Expr e) { return variant(2, e); }

inline Expr mainVariant(Expr e) { return e->right(); }
inline int variantNum(Expr e) {
  const INT &v = dynamic_cast<const INT &>(e->left()->op());
  return v.get();
}

inline Expr prime(Expr e) { return variant(1, e); }
inline bool isPrime(Expr e) { return variantNum(e) == 1; }

/** Creates an expression tagged by another expression (or
    string).  For example, `variant::tag (e, h)` creates an
    expression `e!h`.
*/

inline Expr tag(Expr e, Expr tag) { return mk<TAG>(tag, e); }

inline Expr tag(Expr e, const std::string &t) {
  return tag(e, mkTerm<std::string>(t, e->efac()));
}

inline Expr getTag(Expr e) { return e->left(); }

inline std::string getTagStr(Expr e) { return getTerm<std::string>(getTag(e)); }
} // namespace variant
} // namespace op

namespace op {
NOP_BASE(SimpleTypeOp)

NOP(INT_TY, "INT", PREFIX, SimpleTypeOp)
NOP(CHAR_TY, "CHAR", PREFIX, SimpleTypeOp)
NOP(REAL_TY, "REAL", PREFIX, SimpleTypeOp)
NOP(VOID_TY, "VOID", PREFIX, SimpleTypeOp)
NOP(BOOL_TY, "BOOL", PREFIX, SimpleTypeOp)
/** Uninterpreted Type */
NOP(UNINT_TY, "UNINT", PREFIX, SimpleTypeOp)
/** Array Type */
NOP(ARRAY_TY, "ARRAY", PREFIX, SimpleTypeOp)
} // namespace op

namespace op {
namespace sort {
inline Expr intTy(ExprFactory &efac) { return mk<INT_TY>(efac); }
inline Expr boolTy(ExprFactory &efac) { return mk<BOOL_TY>(efac); }
inline Expr realTy(ExprFactory &efac) { return mk<REAL_TY>(efac); }
inline Expr arrayTy(Expr indexTy, Expr valTy) {
  return mk<ARRAY_TY>(indexTy, valTy);
}

inline Expr arrayIndexTy(Expr a) { return a->left(); }
inline Expr arrayValTy(Expr a) { return a->right(); }
} // namespace sort
} // namespace op

namespace op {
/// Array operators
NOP_BASE(ArrayOp)

NOP(SELECT, "select", FUNCTIONAL, ArrayOp)
NOP(STORE, "store", FUNCTIONAL, ArrayOp)
NOP(CONST_ARRAY, "const-array", FUNCTIONAL, ArrayOp)
NOP(ARRAY_MAP, "array-map", FUNCTIONAL, ArrayOp)
NOP(ARRAY_DEFAULT, "array-default", FUNCTIONAL, ArrayOp)
NOP(AS_ARRAY, "as-array", FUNCTIONAL, ArrayOp)
} // namespace op

namespace op {
namespace array {
inline Expr select(Expr a, Expr idx) { return mk<SELECT>(a, idx); }
inline Expr store(Expr a, Expr idx, Expr v) { return mk<STORE>(a, idx, v); }
inline Expr constArray(Expr domain, Expr v) {
  return mk<CONST_ARRAY>(domain, v);
}
inline Expr aDefault(Expr a) { return mk<ARRAY_DEFAULT>(a); }
} // namespace array
} // namespace op

namespace op {

namespace bind {
struct SCOPE_PS {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "[" << name << " ";
    args[0]->Print(OS, depth + 2, false);
    OS << " in ";
    args[1]->Print(OS, depth + 2, false);
    OS << "]";
  }
};
struct FAPP_PS;
} // namespace bind
NOP_BASE(BindOp)

NOP(BIND, ":", INFIX, BindOp)
/** Function declaration */
NOP(FDECL, "fdecl", PREFIX, BindOp)
/** Function application */
NOP(FAPP, "fapp", bind::FAPP_PS, BindOp)

namespace bind {
inline Expr bind(Expr name, Expr value) { return mk<BIND>(name, value); }
inline Expr name(Expr e) { return e->left(); }
inline Expr type(Expr e) { return e->right(); }
inline Expr value(Expr e) { return e->right(); }

inline Expr var(Expr name, Expr type) { return bind(name, type); }
inline Expr intVar(Expr name) { return var(name, mk<INT_TY>(name->efac())); }
inline Expr realVar(Expr name) { return var(name, mk<REAL_TY>(name->efac())); }
inline Expr boolVar(Expr name) { return var(name, mk<BOOL_TY>(name->efac())); }
inline Expr charVar(Expr name) { return var(name, mk<CHAR_TY>(name->efac())); }
inline Expr unintVar(Expr name) {
  return var(name, mk<UNINT_TY>(name->efac()));
}

template <typename T> bool isVar(Expr v) {
  return isOpX<BIND>(v) && isOpX<T>(bind::type(v));
}
inline bool isBoolVar(Expr v) { return isVar<BOOL_TY>(v); }
inline bool isIntVar(Expr v) { return isVar<INT_TY>(v); }
inline bool isRealVar(Expr v) { return isVar<REAL_TY>(v); }

inline Expr constDecl(Expr name, Expr type) { return mk<FDECL>(name, type); }
inline Expr boolConstDecl(Expr name) {
  return constDecl(name, mk<BOOL_TY>(name->efac()));
}
inline Expr intConstDecl(Expr name) {
  return constDecl(name, mk<INT_TY>(name->efac()));
}
inline Expr realConstDecl(Expr name) {
  return constDecl(name, mk<REAL_TY>(name->efac()));
}

template <typename Range> Expr fdecl(Expr fname, const Range &args) {
  // -- at least one value for range type
  assert(boost::size(args) > 0);
  ExprVector _args;
  _args.push_back(fname);
  _args.insert(_args.end(), boost::begin(args), boost::end(args));
  return mknary<FDECL>(_args);
}

inline bool isFdecl(Expr fdecl) { return isOpX<FDECL>(fdecl); }
inline Expr fname(Expr fdecl) { return fdecl->first(); }

inline Expr fapp(Expr fdecl) { return mk<FAPP>(fdecl); }

template <typename Range> Expr fapp(Expr fdecl, const Range &args) {
  ExprVector _args;
  _args.push_back(fdecl);
  _args.insert(_args.end(), boost::begin(args), boost::end(args));
  return mknary<FAPP>(_args);
}

inline Expr fapp(Expr fdecl, Expr a0, Expr a1 = Expr(), Expr a2 = Expr()) {
  ExprVector args;
  args.push_back(fdecl);

  if (a0)
    args.push_back(a0);
  if (a1)
    args.push_back(a1);
  if (a2)
    args.push_back(a2);
  return mknary<FAPP>(args);
}

inline bool isFapp(Expr fapp) { return isOpX<FAPP>(fapp); }

inline Expr rangeTy(Expr fdecl) { return fdecl->last(); }

inline size_t domainSz(Expr fdecl) {
  assert(fdecl->arity() >= 2);
  return fdecl->arity() - 2;
}

inline Expr domainTy(Expr fdecl, size_t n) {
  assert(n + 2 < fdecl->arity());
  return fdecl->arg(n + 1);
}

template <typename T> bool isFdecl(Expr v) {
  return isOpX<FDECL>(v) && isOpX<T>(rangeTy(v));
}

/** constant is an applied nullary function */
template <typename T> bool isConst(Expr v) {
  return isOpX<FAPP>(v) && v->arity() == 1 && isFdecl<T>(fname(v));
}

inline Expr mkConst(Expr name, Expr sort) {
  return fapp(constDecl(name, sort));
}
inline Expr boolConst(Expr name) { return fapp(boolConstDecl(name)); }
inline Expr intConst(Expr name) { return fapp(intConstDecl(name)); }
inline Expr realConst(Expr name) { return fapp(realConstDecl(name)); }

inline bool isBoolConst(Expr v) { return isConst<BOOL_TY>(v); }
inline bool isIntConst(Expr v) { return isConst<INT_TY>(v); }
inline bool isRealConst(Expr v) { return isConst<REAL_TY>(v); }

inline Expr typeOf(Expr v) {
  using namespace bind;
  if (isOpX<VARIANT>(v))
    return typeOf(variant::mainVariant(v));

  if (isOpX<FAPP>(v)) {
    assert(isOpX<FDECL>(v->left()));
    return rangeTy(v->left());
  }

  if (isOpX<TRUE>(v) || isOpX<FALSE>(v))
    return mk<BOOL_TY>(v->efac());
  if (isOpX<MPZ>(v))
    return mk<INT_TY>(v->efac());
  if (isOpX<MPQ>(v))
    return mk<REAL_TY>(v->efac());

  if (isOpX<BIND>(v))
    return bind::type(v);

  if (isBoolVar(v) || isBoolConst(v))
    return mk<BOOL_TY>(v->efac());
  if (isIntVar(v) || isIntConst(v))
    return mk<INT_TY>(v->efac());
  if (isRealVar(v) || isRealConst(v))
    return mk<REAL_TY>(v->efac());

  if (isOpX<SELECT>(v)) {
    Expr a = v->left();
    if (isOpX<FAPP>(a)) {
      Expr decl_a = a->left(); // decl_a is fdecl name (ARRAY idxTy valTy)
      Expr array_ty = decl_a->right();
      Expr val_ty = array_ty->right();
      return val_ty;
    }
  }

  // if (isOpX<STORE>(v)) {
  //   Expr a = v->left();
  //   if (isOpX<FAPP> (a)) {
  //     Expr decl_a = a->left(); // decl_a is fdecl name (ARRAY idxTy valTy)
  //     Expr array_ty = decl_a->right();
  //     return array_ty;
  //   }
  // }

  std::cerr << "WARNING: could not infer type of: " << *v << "\n";
  assert(0 && "Unreachable");
  return Expr();
}
inline Expr sortOf(Expr v) { return typeOf(v); }

struct FAPP_PS {
  static inline void print(std::ostream &OS, int depth, int brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    if (args.size() > 1)
      OS << "(";

    // -- strip fdecl if there is one
    ENode *fname = args[0];
    if (isOpX<FDECL>(fname))
      fname = fname->arg(0);
    fname->Print(OS, depth + 2, false);

    for (unsigned i = 1; i < args.size(); ++i) {
      OS << " ";
      args[i]->Print(OS, depth + 2, false);
    }

    if (args.size() > 1)
      OS << ")";
  }
};

/// Creates a new fdecl with the same signature as the given
/// fdecl and a new name
inline Expr rename(Expr fdecl, Expr name) {
  assert(isOpX<FDECL>(fdecl));
  ExprVector _args;
  _args.reserve(fdecl->arity());
  _args.push_back(name);
  _args.insert(_args.end(), ++(fdecl->args_begin()), fdecl->args_end());
  return mknary<FDECL>(_args);
}

/// construct a new expression by applying fdecl to the same
/// arguments as fapp. For example, reapp of g(a,b) and f is f(a, b)
inline Expr reapp(Expr fapp, Expr fdecl) {
  assert(isOpX<FDECL>(fdecl));
  assert(isOpX<FAPP>(fapp));

  ExprVector _args;
  _args.reserve(fapp->arity());
  _args.push_back(fdecl);
  _args.insert(_args.end(), ++(fapp->args_begin()), fapp->args_end());
  return mknary<FAPP>(_args);
}

} // namespace bind

namespace bind {
/// returns true if an expression is a constant
class IsConst : public std::unary_function<Expr, bool> {
public:
  bool operator()(Expr e) {
    if (isOpX<VARIANT>(e))
      return this->operator()(variant::mainVariant(e));

    return isOpX<FAPP>(e) && e->arity() == 1 && isOpX<FDECL>(fname(e));
  }
};
} // namespace bind
} // namespace op
} // namespace expr

namespace expr {
namespace op {
namespace bind {
struct BoundVar {
  unsigned var;

  BoundVar(unsigned v) : var(v) {}
  BoundVar(const BoundVar &o) : var(o.var) {}

  bool operator<(const BoundVar &b) const { return var < b.var; }
  bool operator==(const BoundVar &b) const { return var == b.var; }
  bool operator!=(const BoundVar &b) const { return var != b.var; }

  size_t hash() const {
    std::hash<unsigned> hasher;
    return hasher(var);
  }

  void Print(std::ostream &OS) const { OS << "B" << var; }
};
inline std::ostream &operator<<(std::ostream &OS, const BoundVar &b) {
  b.Print(OS);
  return OS;
}
} // namespace bind
} // namespace op

template <> struct TerminalTrait<op::bind::BoundVar> {
  static inline void print(std::ostream &OS, const op::bind::BoundVar &b,
                           int depth, bool brkt) {
    OS << b;
  }
  static inline bool less(const op::bind::BoundVar &b1,
                          const op::bind::BoundVar &b2) {
    return b1 < b2;
  }

  static inline bool equal_to(const op::bind::BoundVar &b1,
                              const op::bind::BoundVar &b2) {
    return b1 == b2;
  }

  static inline size_t hash(const op::bind::BoundVar &b) { return b.hash(); }
};

namespace op {
typedef Terminal<bind::BoundVar> BVAR;

namespace bind {
inline Expr bvar(unsigned idx, Expr type) {
  return var(mkTerm(BoundVar(idx), type->efac()), type);
}
inline Expr intBVar(unsigned idx, ExprFactory &efac) {
  return intVar(mkTerm(BoundVar(idx), efac));
}
inline Expr boolBVar(unsigned idx, ExprFactory &efac) {
  return boolVar(mkTerm(BoundVar(idx), efac));
}
inline Expr realBVar(unsigned idx, ExprFactory &efac) {
  return realVar(mkTerm(BoundVar(idx), efac));
}
inline Expr unintBVar(unsigned idx, ExprFactory &efac) {
  return unintVar(mkTerm(BoundVar(idx), efac));
}

inline bool isBVar(Expr e) {
  return isOpX<BIND>(e) && isOpX<BVAR>(bind::name(e));
}

inline unsigned bvarId(Expr e) {
  Expr t = e;
  if (isBVar(e))
    t = bind::name(e);
  assert(isOpX<BVAR>(t));
  return getTerm<BoundVar>(t).var;
}

} // namespace bind
} // namespace op

namespace details {
template <typename Range> Expr absConstants(const Range &r, Expr e);

template <typename Range> Expr subBndVars(const Range &r, Expr e);
} // namespace details

namespace op {

/**
    Binders with Locally Nameless representation.

    Arthur Charguéraud: The Locally Nameless
    Representation. J. Autom. Reasoning 49(3): 363-408 (2012)
 */

namespace bind {
struct BINDER {
  static inline void print(std::ostream &OS, int depth, bool brkt,
                           const std::string &name,
                           const std::vector<ENode *> &args) {
    OS << "(" << name << " ";

    OS << "(";
    for (auto it = args.begin(), end = args.end() - 1; it != end; ++it) {
      (*it)->last()->Print(OS, depth + 2, true);
      if (it + 1 != end)
        OS << " ";
    }
    OS << ") ";

    args.back()->Print(OS, depth + 2, true);

    OS << ")";
  }
};
} // namespace bind

NOP_BASE(BinderOp)
/** Forall quantifier */
NOP(FORALL, "forall", bind::BINDER, BinderOp)
/** Exists */
NOP(EXISTS, "exists", bind::BINDER, BinderOp)
/** Lambda */
NOP(LAMBDA, "lambda", bind::BINDER, BinderOp)

namespace bind {
inline unsigned numBound(Expr e) {
  assert(e->arity() > 0);
  return e->arity() - 1;
}
inline Expr decl(Expr e, unsigned i) { return e->arg(i); }
inline Expr boundName(Expr e, unsigned i) { return fname(decl(e, i)); }
inline Expr boundSort(Expr e, unsigned i) { return rangeTy(decl(e, i)); }

inline Expr body(Expr e) { return *(--(e->args_end())); }

template <typename Op, typename Range> Expr abs(const Range &r, Expr e) {
  Expr abs = expr::details::absConstants(r, e);
  if (abs == e)
    return e;

  ExprVector args;
  args.reserve(std::distance(std::begin(r), std::end(r)) + 1);
  for (auto &v : r) {
    assert(bind::IsConst()(v));
    args.push_back(bind::fname(v));
  }

  args.push_back(abs);

  return mknary<Op>(args);
}

template <typename Op> Expr abs(Expr v, Expr e) {
  std::array<Expr, 1> a = {v};
  return abs<Op>(a, e);
}

template <typename Op> Expr abs(Expr v0, Expr v1, Expr e) {
  std::array<Expr, 2> a = {v0, v1};
  return abs<Op>(a, e);
}

template <typename Op> Expr abs(Expr v0, Expr v1, Expr v2, Expr e) {
  std::array<Expr, 3> a = {v0, v1, v2};
  return abs<Op>(a, e);
}

template <typename Range> Expr sub(const Range &r, Expr e) {
  return expr::details::subBndVars(r, e);
}

inline Expr sub(Expr v0, Expr e) {
  std::array<Expr, 1> a = {v0};
  return sub(a, e);
}

inline Expr sub(Expr v0, Expr v1, Expr e) {
  std::array<Expr, 2> a = {v0, v1};
  return sub(a, e);
}

inline Expr sub(Expr v0, Expr v1, Expr v2, Expr e) {
  std::array<Expr, 3> a = {v0, v1, v2};
  return sub(a, e);
}

template <typename Range> Expr betaReduce(Expr lambda, const Range &r) {
  // -- nullptr
  if (!lambda)
    return lambda;
  // -- not lambda
  if (!isOpX<LAMBDA>(lambda))
    return lambda;

  // -- nullary
  if (numBound(lambda) == 0)
    return body(lambda);

  // -- number of arguments must match number of bound variables
  assert(std::distance(std::begin(r), std::end(r)) == numBound(lambda));

  // -- replace bound variables
  // XXX Need to decide on the order, this might be opposite from what clients
  // expect
  return sub(r, body(lambda));
}

inline Expr betaReduce(Expr lambda, Expr v0) {
  std::array<Expr, 1> a = {v0};
  return betaReduce(lambda, a);
}
inline Expr betaReduce(Expr lambda, Expr v0, Expr v1) {
  std::array<Expr, 2> a = {v0, v1};
  return betaReduce(lambda, a);
}
inline Expr betaReduce(Expr lambda, Expr v0, Expr v1, Expr v2) {
  std::array<Expr, 3> a = {v0, v1, v2};
  return betaReduce(lambda, a);
}
inline Expr betaReduce(Expr lambda, Expr v0, Expr v1, Expr v2, Expr v3) {
  std::array<Expr, 4> a = {v0, v1, v2, v3};
  return betaReduce(lambda, a);
}
} // namespace bind
} // namespace op

/**********************************************************************/
/* Visitors */
/**********************************************************************/
namespace {
/* Visitors are hidden. Only to be used internally. */

struct RAV : public std::unary_function<Expr, VisitAction> {
  Expr s;
  Expr t;

  RAV(const RAV &o) : s(o.s), t(o.t) {}
  RAV(Expr _s, Expr _t) : s(_s), t(_t) {}
  VisitAction operator()(Expr exp) const {
    return exp == s ? VisitAction::changeTo(t) : VisitAction::doKids();
  }
};

struct RAVSIMP : public std::unary_function<Expr, VisitAction> {
  Expr s;
  Expr t;

  std::shared_ptr<boolop::TrivialSimplifier> r;

  RAVSIMP(const RAVSIMP &o) : s(o.s), t(o.t), r(o.r) {}
  RAVSIMP(Expr _s, Expr _t)
      : s(_s), t(_t),
        r(std::make_shared<boolop::TrivialSimplifier>(s->efac())) {}

  VisitAction operator()(Expr exp) const {
    if (exp == s)
      return VisitAction::changeTo(t);
    return VisitAction::changeDoKidsRewrite(exp, r);
  }
};

template <typename F, typename OutputIterator>
struct FV : public std::unary_function<Expr, VisitAction> {
  F filter;

  OutputIterator out;
  ExprSet seen;

  typedef FV<F, OutputIterator> this_type;
  FV(const this_type &o) : filter(o.filter), out(o.out), seen(o.seen) {
    assert(0);
  }

  FV(F f, OutputIterator o) : filter(f), out(o) {}
  VisitAction operator()(Expr exp) {
    if (seen.count(exp) > 0)
      return VisitAction::skipKids();
    seen.insert(exp);

    if (filter(exp)) {
      *(out++) = exp;
      return VisitAction::skipKids();
    }

    return VisitAction::doKids();
  }
};

template <typename M>
struct RV : public std::unary_function<Expr, VisitAction> {
  typedef typename M::const_iterator const_iterator;

  const M &map;
  RV(const M &m) : map(m) {}
  VisitAction operator()(Expr exp) const {
    const_iterator it = map.find(exp);

    return it == map.end() ? VisitAction::doKids()
                           : VisitAction::changeTo(it->second);
  }
};

template <typename M>
struct RVSIMP : public std::unary_function<Expr, VisitAction> {
  typedef typename M::const_iterator const_iterator;

  const M &map;

  std::shared_ptr<boolop::TrivialSimplifier> r;

  typedef RVSIMP<M> this_type;

  RVSIMP(const this_type &o) : map(o.map), r(o.r) {}
  RVSIMP(ExprFactory &fac, const M &m)
      : map(m), r(std::make_shared<boolop::TrivialSimplifier>(fac)) {}

  VisitAction operator()(Expr exp) const {
    const_iterator it = map.find(exp);

    if (it == map.end())
      return VisitAction::changeDoKidsRewrite(exp, r);

    return VisitAction::changeTo(it->second);
  }
};

struct CV : public std::unary_function<Expr, VisitAction> {
  Expr e;
  bool found;
  ExprSet seen;

  CV(const CV &o) : e(o.e), found(o.found), seen(o.seen) { assert(0); }

  CV(Expr exp) : e(exp), found(false) {}

  VisitAction operator()(Expr exp) {
    if (found || seen.count(exp) > 0 || e == exp) {
      found = true;
      return VisitAction::skipKids();
    }
    seen.insert(e);
    return VisitAction::doKids();
  }
};

struct SIZE : public std::unary_function<Expr, VisitAction> {
  size_t count;

  SIZE() : count(0) {}

  VisitAction operator()(Expr exp) {
    count++;
    return VisitAction::doKids();
  }
};

template <typename T>
struct RW : public std::unary_function<Expr, VisitAction> {
  std::shared_ptr<T> _r;

  typedef RW<T> this_type;

  RW(const this_type &o) : _r(o._r) {}
  RW(std::shared_ptr<T> r) : _r(r) {}

  VisitAction operator()(Expr exp) {
    return VisitAction::changeDoKidsRewrite(exp, _r);
  }
};

} // namespace

/**********************************************************************/
/* Utility Functions */
/**********************************************************************/

/** Applies a rewriter */
template <typename T> Expr rewrite(std::shared_ptr<T> r, Expr e) {
  RW<T> rw(r);
  return dagVisit(rw, e);
}

/** Size of an expression as a DAG */
inline size_t dagSize(Expr e) {
  SIZE sz;
  dagVisit(sz, e);
  return sz.count;
}

inline size_t dagSize(const ExprVector &vec) {
  SIZE sz;
  dagVisit(sz, vec);
  return sz.count;
}

/** Size of an expression as a tree */
inline size_t treeSize(Expr e) {
  SIZE sz;
  visit(sz, e);
  return sz.count;
}

// -- replace all occurrences of s by t
inline Expr replaceAll(Expr exp, Expr s, Expr t) {
  RAV rav(s, t);
  return dagVisit(rav, exp);
}

/** Replace all occurrences of s by t while simplifying the result */
inline Expr replaceAllSimplify(Expr exp, Expr s, Expr t) {
  RAVSIMP rav(s, t);
  return dagVisit(rav, exp);
}

// -- collect all sub-expressions of exp that satisfy the filter
template <typename F, typename OutputIterator>
void filter(Expr exp, F filter, OutputIterator out) {
  FV<F, OutputIterator> fv(filter, out);
  dagVisit(fv, exp);
}

// template <typename F>
// void filter (Expr exp, F f, ExprSet &out)
// {
//   filter (exp, f, std::inserter (out, out.begin ()));
// }

/** A wrapper to use any functional object as a replace-map */
template <typename F> struct fn_map {
  struct const_iterator {
    ExprPair pair;
    const_iterator() : pair(Expr(), Expr()) {}

    const_iterator(Expr u, Expr v) : pair(u, v) {}

    bool operator==(const const_iterator &other) const {
      return pair == other.pair;
    }

    const ExprPair &operator*() const { return pair; }
    const ExprPair *operator->() const { return &pair; }
  };

  const_iterator end_iterator;

  /** the function */
  F f;
  fn_map(const F &fn) : f(fn) {}

  const_iterator find(Expr exp) const {
    Expr res = f(exp);
    if (res)
      return const_iterator(exp, res);
    return end();
  }

  const_iterator end() const { return end_iterator; }
};

template <typename F> fn_map<F> mk_fn_map(const F &fn) { return fn_map<F>(fn); }

template <typename M> Expr replace(Expr exp, const M &map) {
  RV<M> rv(map);
  return dagVisit(rv, exp);
}

/** Replace and simplify */
template <typename M> Expr replaceSimplify(Expr exp, const M &map) {
  RVSIMP<M> rv(exp->efac(), map);
  return dagVisit(rv, exp);
}

/** Returns true if e1 contains e2 as a sub-expression */
inline bool contains(Expr e1, Expr e2) {
  CV cv(e2);
  dagVisit(cv, e1);
  return cv.found;
}

namespace op {
namespace boolop {
namespace {
template <typename T> struct BS {
  std::shared_ptr<T> _r;

  BS(std::shared_ptr<T> r) : _r(r) {}
  BS(T *r) : _r(r) {}

  VisitAction operator()(Expr exp) {
    // -- apply the rewriter
    if (isOp<BoolOp>(exp))
      return VisitAction::changeDoKidsRewrite(exp, _r);

    // -- do not descend into non-boolean operators
    return VisitAction::skipKids();
  }
};
} // namespace

/**
 * Very simple simplifier for Boolean Operators
 */
inline Expr simplify(Expr exp) {
  BS<TrivialSimplifier> bs(std::make_shared<TrivialSimplifier>(exp->efac()));
  return dagVisit(bs, exp);
}

/**
 * Very simple normalizer for AND/OR expressions
 */
inline Expr norm(Expr exp) {
  BS<NormalizeOps> bs(new NormalizeOps());
  return dagVisit(bs, exp);
}

/** Gather binary Boolean operators into n-ary ones. Helps
    readability. Best done after NNF */
inline Expr gather(Expr exp) {
  BS<GatherOps> go(new GatherOps());
  return dagVisit(go, exp);
}

/**
 * Converts to NNF. Assumes the only Boolean operators of exp
 * are AND/OR/NEG.
 */
inline Expr nnf(Expr exp) {
  NNF n(exp->efac());
  return dagVisit(n, exp);
}

/** Makes an expression pretty for printing */
inline Expr pp(Expr exp) { return gather(nnf(exp)); }

} // namespace boolop
} // namespace op
} // namespace expr

#include "ExprBv.hh"

namespace std {
/** standard order of expressions by their id */
template <> struct less<expr::ENode *> {
  bool operator()(const expr::ENode *x, const expr::ENode *y) const {
    if (x == NULL)
      return y != NULL;
    if (y == NULL)
      return false;

    return x->getId() < y->getId();
  }
};

} // namespace std

#include <boost/bimap.hpp>
#include <boost/bimap/list_of.hpp>
#include <boost/bimap/unordered_set_of.hpp>
namespace expr {
using namespace boost;

/** LRU Cache */
template <typename T> class ExprCache {
  typedef boost::bimaps::bimap<boost::bimaps::unordered_set_of<ENode *>,
                               boost::bimaps::list_of<T>>
      cache_type;
  typedef typename cache_type::left_value_type value_type;
  typedef typename cache_type::right_iterator right_iterator;

  cache_type cache;
  size_t capacity;

public:
  typedef typename cache_type::left_const_iterator const_iterator;
  typedef typename cache_type::left_iterator iterator;

public:
  ExprCache(size_t c) : capacity(c) {}

  ~ExprCache() { clear(); }

  void clear() {
    for (iterator it = cache.left.begin(), end = cache.left.end(); it != end;
         ++it) {
      ENode *n = it->first;
      n->efac().Deref(n);
    }
    cache.clear();
  }

  const_iterator find(Expr e) {
    const_iterator it = cache.left.find(&*e);
    if (it != cache.left.end())
      cache.right.relocate(cache.right.end(), cache.project_right(it));
    return it;
  }

  const_iterator end() const { return cache.left.end(); }

  std::pair<iterator, bool> insert(Expr e, T &v) {
    if (cache.size() == capacity) {
      right_iterator it = cache.right.begin();
      // -- dereference a key that is about to be deleted
      ENode *old = it->second;
      old->efac().Deref(old);
      cache.right.erase(it);
    }
    ENode *n = &*e;
    n->Ref();
    return cache.left.insert(value_type(n, v));
  }

  size_t size() const { return cache.size(); }
};
} // namespace expr

namespace expr {
inline size_t hash_value(Expr e) {
  std::hash<ENode *> hasher;
  return hasher(e.get());
}
} // namespace expr

/// implement boost::hash
namespace boost {
template <>
struct hash<expr::Expr> : public std::unary_function<expr::Expr, std::size_t> {
  std::size_t operator()(const expr::Expr &v) const {
    return expr::hash_value(v);
  }
};
} // namespace boost

/// implement std::hash
namespace std {
template <>
struct hash<expr::Expr> : public std::unary_function<expr::Expr, std::size_t> {
  std::size_t operator()(const expr::Expr &v) const {
    return expr::hash_value(v);
  }
};
} // namespace std

namespace expr {
namespace details {
template <typename Abs> struct ABSCST;

template <typename Range> struct AbsCst {
  typedef AbsCst<Range> this_type;

  const Range &m_r;
  std::unordered_map<Expr, unsigned> m_evmap;

  std::vector<ABSCST<this_type>> m_pinned;

  typedef std::map<unsigned, DagVisit<ABSCST<this_type>>> cache_type;
  cache_type m_cache;

  AbsCst(const Range &r);
  DagVisit<ABSCST<this_type>> &cachedVisitor(unsigned offset);
};

template <typename Abs>
struct ABSCST : public std::unary_function<Expr, VisitAction> {
  Abs &m_a;
  unsigned m_offset;

  inline ABSCST(Abs &a, unsigned offset);
  inline VisitAction operator()(Expr exp) const;
};

template <typename Range> AbsCst<Range>::AbsCst(const Range &r) : m_r(r) {
  unsigned cnt = std::distance(std::begin(r), std::end(r));
  for (const Expr &v : m_r)
    m_evmap[v] = --cnt;
}

template <typename Range>
DagVisit<ABSCST<AbsCst<Range>>> &AbsCst<Range>::cachedVisitor(unsigned offset) {
  typedef AbsCst<Range> this_type;

  auto it = m_cache.find(offset);
  if (it != m_cache.end())
    return it->second;

  m_pinned.push_back(ABSCST<this_type>(*this, offset));

  auto v = m_cache.insert(
      std::make_pair(offset, DagVisit<ABSCST<this_type>>(m_pinned.back())));
  return (v.first)->second;
}

template <typename Abs>
ABSCST<Abs>::ABSCST(Abs &a, unsigned offset) : m_a(a), m_offset(offset) {}

template <typename Abs> VisitAction ABSCST<Abs>::operator()(Expr exp) const {
  if (op::bind::isFdecl(exp))
    return VisitAction::skipKids();

  if (op::bind::IsConst()(exp)) {
    auto it = m_a.m_evmap.find(exp);
    if (it != m_a.m_evmap.end()) {
      Expr b = bind::bvar(m_offset + it->second, bind::sortOf(exp));
      return VisitAction::changeTo(b);
    }
    return VisitAction::skipKids();
  } else if (isOp<BinderOp>(exp)) {
    auto &dv = m_a.cachedVisitor(m_offset + 1);
    ExprVector kids(exp->args_begin(), exp->args_end());
    Expr &last = kids.back();
    last = dv(last);
    return VisitAction::changeTo(exp->efac().mkNary(exp->op(), kids));
  }

  return VisitAction::doKids();
}

template <typename Range> Expr absConstants(const Range &r, Expr e) {
  AbsCst<Range> a(r);
  auto v = ABSCST<AbsCst<Range>>(a, 0);
  return dagVisit(v, e);
}

template <typename Sub> struct SUBBND;

template <typename Range> struct SubBnd {
  typedef SubBnd<Range> this_type;

  const Range &m_r;
  unsigned m_sz;
  std::vector<SUBBND<this_type>> m_pinned;
  typedef std::map<unsigned, DagVisit<SUBBND<this_type>>> cache_type;
  cache_type m_cache;

  SubBnd(const Range &r) : m_r(r) {
    m_sz = std::distance(std::begin(m_r), std::end(m_r));
  }

  DagVisit<SUBBND<this_type>> &cachedVisitor(unsigned offset);

  Expr sub(unsigned idx) {
    if (idx >= m_sz)
      return Expr(0);
    auto it = std::end(m_r) - 1 - idx;
    return *it;
  }
};

template <typename Sub>
struct SUBBND : public std::unary_function<Expr, VisitAction> {
  Sub &m_a;
  unsigned m_offset;

  SUBBND(Sub &a, unsigned offset) : m_a(a), m_offset(offset){};

  VisitAction operator()(Expr exp) const {
    if (bind::isFdecl(exp))
      return VisitAction::skipKids();
    else if (bind::isBVar(exp)) {
      unsigned idx = bind::bvarId(exp);
      if (idx < m_offset)
        return VisitAction::skipKids();

      Expr u = m_a.sub(idx - m_offset);
      return u ? VisitAction::changeTo(u) : VisitAction::skipKids();
    } else if (isOp<BinderOp>(exp)) {
      auto &dv = m_a.cachedVisitor(m_offset + 1);
      ExprVector kids(exp->args_begin(), exp->args_end());
      Expr &last = kids.back();
      last = dv(last);
      return VisitAction::changeTo(exp->efac().mkNary(exp->op(), kids));
    }
    return VisitAction::doKids();
  }
};

template <typename Range>
DagVisit<SUBBND<SubBnd<Range>>> &SubBnd<Range>::cachedVisitor(unsigned offset) {
  typedef SubBnd<Range> this_type;
  auto it = m_cache.find(offset);
  if (it != m_cache.end())
    return it->second;

  m_pinned.push_back(SUBBND<this_type>(*this, offset));
  auto v = m_cache.insert(
      std::make_pair(offset, DagVisit<SUBBND<this_type>>(m_pinned.back())));
  return (v.first)->second;
}

template <typename Range> Expr subBndVars(const Range &r, Expr e) {
  SubBnd<Range> a(r);
  auto v = SUBBND<SubBnd<Range>>(a, 0);
  return dagVisit(v, e);
}
} // namespace details
} // namespace expr

#endif
