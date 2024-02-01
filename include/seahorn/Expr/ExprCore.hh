/// Core of the Expr library
#pragma once

#include <boost/functional/hash_fwd.hpp>
#include <boost/intrusive_ptr.hpp>
#include <boost/pool/pool.hpp>
#include "seahorn/boost_ptr_vector.hh"

#include <iostream>
#include <map>
#include <set>
#include <unordered_set>
#include <vector>
namespace expr {

namespace op {}
using namespace expr::op;

class ENode;
class ExprFactory;
class ExprFactoryAllocator;
class TypeChecker;

using Expr = boost::intrusive_ptr<ENode>;
using ExprSet = std::set<Expr>;
using ExprVector = std::vector<Expr>;
using ExprPair = std::pair<Expr, Expr>;
using ExprMap = std::map<Expr, Expr>;

/* Helper functions to convert from different wrappers over
   expressions into a pointer to an expression node */
inline ENode *eptr(ENode *p) { return p; }
inline const ENode *eptr(const ENode *p) { return p; }
inline ENode *eptr(ENode &p) { return &p; }
inline const ENode *eptr(const ENode &p) { return &p; }
inline ENode *eptr(const Expr &e) { return e.get(); }
inline ENode *eptr(Expr &e) { return e.get(); }

enum class OpFamilyId {
  Terminal,
  BoolOp,
  CompareOp,
  NumericOp,
  MiscOp,
  SimpleTypeOp,
  TerminalTypeOp,
  ArrayOp,
  StructOp,
  FiniteMapOp,
  VariantOp,
  BindOp,
  BinderOp,
  BvOp,
  GateOp,
  MutModelOp,
  ErrorBinderOp,
};

/// \brief An operator labeling a node of an expression tree
class Operator {
  /// \brief Family to which the operator belongs
  OpFamilyId m_familyId;

public:
  /// \brief No default constructor
  Operator() = delete;
  Operator(OpFamilyId family) : m_familyId(family) {}
  virtual ~Operator(){};

  /// \brief Return family of the operator
  OpFamilyId getFamilyId() const { return m_familyId; }

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
  /// \brief Returns heap-allocted copy of the operator
  virtual Operator *clone(ExprFactoryAllocator &allocator) const = 0;
  virtual std::string name() const = 0;
  /// \return true for the typechecker to infer the type of the current
  /// expression before visiting its children
  virtual bool typeCheckTopDown() const = 0;
  /// \brief Returns the type of the expression
  virtual Expr inferType(Expr exp, TypeChecker &tc) const = 0;
};

inline std::ostream &operator<<(std::ostream &OS, const Operator &V) {
  std::vector<ENode *> x;
  V.Print(OS, x);
  return OS;
}

struct EFADeleter {
  ExprFactoryAllocator *m_efa;
  EFADeleter(ExprFactoryAllocator &efa) : m_efa(&efa) {}
  EFADeleter(const EFADeleter &) = default;
  EFADeleter &operator=(const EFADeleter &o) = default;
  void operator()(void *p);
};

/// \brief An expression tree node
class ENode {
protected:
  /** unique identifier of this expression node */
  unsigned int id;
  /** reference counter */
  unsigned int count;

  /// \brief Parent factory that created this node
  ExprFactory *fac;

  /// \brief Pointer to children / arguments of this node
  std::vector<ENode *> args;

  /// \brief Operator labeling the node
  std::unique_ptr<Operator, EFADeleter> m_oper;

  void Deref() {
    if (count > 0)
      count--;
  }

  /// \brief Set id of the node
  void setId(unsigned int v) { id = v; }

public:
  ENode(ExprFactory &f, const Operator &o);
  ~ENode();

  ENode() = delete;
  ENode(const ENode &) = delete;

  ExprFactory &getFactory() const { return *fac; }
  ExprFactory &efac() const { return getFactory(); }

  /** returns the unique id of this expression */
  unsigned int getId() const { return id; }

  void Ref() { count++; }
  bool isGarbage() const { return count == 0; }
  bool isMutable() const { return m_oper->isMutable(); }

  unsigned int use_count() { return count; }

  ENode *operator[](size_t p) { return arg(p); }
  ENode *arg(size_t p) { return args[p]; }

  ENode *left() { return (args.size() > 0) ? args[0] : nullptr; }

  ENode *right() { return (args.size() > 1) ? args[1] : nullptr; }

  ENode *first() { return left(); }
  ENode *last() { return args.size() > 0 ? args[args.size() - 1] : nullptr; }

  using args_const_iterator = std::vector<ENode *>::const_iterator;

  bool args_empty() const { return args.empty(); }
  args_const_iterator args_begin() const { return args.begin(); }
  args_const_iterator args_end() const { return args.end(); }

  args_const_iterator begin() const { return args_begin(); }
  args_const_iterator end() const { return args_end(); }

  template <typename iterator> void renew_args(iterator b, iterator e);

  void push_back(ENode *a) {
    args.push_back(a);
    a->Ref();
  }

  size_t arity() const { return args.size(); }

  const Operator &op() const { return *m_oper; }
  void Print(std::ostream &OS, int depth = 0, bool brkt = true) const {
    m_oper->Print(OS, args, depth, brkt);
  }
  void dump() const {
    Print(std::cerr, 0, false);
    std::cerr << std::endl;
  }

  friend class ExprFactory;
  friend struct std::less<expr::ENode *>;
};

inline std::ostream &operator<<(std::ostream &OS, const ENode &V) {
  V.Print(OS);
  return OS;
}
inline std::ostream &operator<<(std::ostream &OS, const ENode *v) {
  if (v == nullptr)
    OS << "nullptr";
  else
    OS << *v;
  return OS;
}

/// \brief Hash function used by ExprFactory
struct ENodeUniqueHash {
  std::size_t operator()(const ENode *e) const {
    size_t res = e->op().hash();

    size_t a = e->arity();
    if (a == 0)
      return res;

    auto it = e->args_begin();
    if (a >= 1)
      boost::hash_combine(res, *it);

    if (a >= 2)
      boost::hash_combine(res, boost::hash_range(it, e->args_end()));

    return res;
  }
};

/// \brief Equality function used by ExprFactory
struct ENodeUniqueEqual {
  bool operator()(ENode *const &e1, ENode *const &e2) const {
    // same arity, same operator, identical children
    if (e1->arity() == e2->arity() && e1->op() == e2->op())
      return std::equal(e1->args_begin(), e1->args_end(), e2->args_begin());

    return false;
  }
};

/// \brief Type erasure for Cache
struct CacheStub {
  /// brief Returns true if the stub own the cahce pointer by pointer \p p
  virtual bool owns(const void *p) = 0;
  /// \brief Removes a given value \p val from the cache
  virtual void erase(ENode *val) = 0;

  CacheStub() = default;
  virtual ~CacheStub() = default;
};

template <typename C> struct CacheStubImpl : CacheStub {

  C &m_cache;

  CacheStubImpl(C &c) : m_cache(c){};

  virtual bool owns(const void *p) {
    return p == static_cast<const void *>(&m_cache);
  }
  virtual void erase(ENode *val) { m_cache.erase(val); }
};

class ExprFactoryAllocator {
private:
  /** pool for tiny objects */
  boost::pool<> tiny;
  /** pool for small objects */
  boost::pool<> small;

public:
  ExprFactoryAllocator() : tiny(8, 65536), small(64, 65536){};
  ExprFactoryAllocator(const ExprFactoryAllocator &) = delete;

  void *allocate(size_t n);
  void free(void *block);

  EFADeleter get_deleter();
};

class ExprFactory : boost::noncopyable {
protected:
  using unique_entry_type =
      std::unordered_set<ENode *, ENodeUniqueHash, ENodeUniqueEqual>;

  using unique_key_type = std::string;
  // -- type of the unique table
  using unique_type = std::map<unique_key_type, unique_entry_type>;

  using caches_type = boost::ptr_vector<CacheStub>;

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
      unique_type::iterator it = unique.find(val->op().name());
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
   * Return the canonical (unique) representetive of the given ENode \p v
   * The node \p v should not be used after the call
   */
  ENode *canonize(ENode *v) {
    if (v->isMutable()) {
      v->setId(uniqueId());
      return v;
    }

    auto x = unique[v->op().name()].insert(v);
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

  /** n-ary
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

  /*===================== PUBLIC API ========================================*/

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
    caches.push_back(static_cast<CacheStub *>(new CacheStubImpl<Cache>(cache)));
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
    : count(0), fac(&f),
      m_oper(o.clone(f.allocator), f.allocator.get_deleter()) {}

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
    n->m_oper.reset();

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
  res->m_oper = std::unique_ptr<Operator, EFADeleter>(op.clone(allocator),
                                                      allocator.get_deleter());
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

inline void EFADeleter::operator()(void *p) { operator delete(p, *m_efa); }

template <typename iterator> void ENode::renew_args(iterator b, iterator e) {
  std::vector<ENode *> old = args;
  args = std::vector<ENode *>();

  // -- increment reference count of all new arguments
  for (; b != e; ++b)
    this->push_back(eptr(*b));

  // -- decrement reference count of all old arguments
  for (auto b = old.begin(), e = old.end(); b != e; ++b)
    efac().Deref(*b);
}

inline ENode::~ENode() {
  for (auto b = args.begin(), e = args.end(); b != e; ++b)
    efac().Deref(*b);
}

/** Required by boost::intrusive_ptr */
inline void intrusive_ptr_add_ref(ENode *v) { v->Ref(); }

inline void intrusive_ptr_release(ENode *v) { v->efac().Deref(v); }

} // namespace expr

// ========================== HASHING ======================================
namespace expr {
inline size_t hash_value(Expr e) {
  if (!e)
    return 0;
  std::hash<unsigned int> hasher;
  return hasher(e->getId());
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

/// implement std::hash<expr::Expr>
namespace std {
template <>
struct hash<expr::Expr> : public std::unary_function<expr::Expr, std::size_t> {
  std::size_t operator()(const expr::Expr &v) const {
    return expr::hash_value(v);
  }
};
} // namespace std

/// std::less<expr::ENode*>
namespace std {
/** standard order of expressions by their id */
template <> struct less<expr::ENode *> {
  bool operator()(const expr::ENode *x, const expr::ENode *y) const {
    if (x == nullptr)
      return y != nullptr;
    if (y == nullptr)
      return false;

    return x->getId() < y->getId();
  }
};
} // namespace std
