#ifndef __SYM_STORE_HH_
#define __SYM_STORE_HH_
/// A symbolic store is a map from symbolic registers to symbolic values.

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/ExprVisitor.hh"

#include "llvm/Support/raw_ostream.h"
#include <map>
#include <memory>
#include <unordered_map>

namespace seahorn {
using namespace expr;

class SymStore;

namespace detail {
using namespace expr;

struct SymStoreEvalVisitor : public std::unary_function<Expr, VisitAction> {
  SymStore &m_store;

  SymStoreEvalVisitor(SymStore &s) : m_store(s) {}
  VisitAction operator()(Expr exp) const;
};

struct scoped_track_use {
  SymStore &m_s;
  bool m_trackUse;

  scoped_track_use(SymStore &s, bool trackUse);
  ~scoped_track_use();
};
} // namespace detail

class SymStore : public std::unary_function<Expr, Expr> {
  friend struct detail::scoped_track_use;

public:
  typedef std::shared_ptr<SymStore> SymStorePtr;
  typedef std::unordered_map<Expr, Expr> ExprExprMap;

protected:
  /// Parent store, if any
  SymStore *m_Parent;
  /// shared pointer for a parent if owned by this object
  SymStorePtr m_ownedParent;

  /// The store
  ExprExprMap m_Store;

  ExprFactory &m_efac;

  bool m_trackUse;

  ExprVector m_uses;
  ExprVector m_defs;
  size_t m_defs_sz;

  detail::SymStoreEvalVisitor m_evalVisitor;

public:
  /// Create a SymStore with a given parent store. This store
  /// delegates all havocs() and unknown reads() to the parent.
  /// trackUse indicates whether the store should keep track of all
  /// reads and writes.
  SymStore(SymStore &parent, bool trackUse)
      : m_Parent(&parent), m_efac(m_Parent->getExprFactory()),
        m_trackUse(trackUse), m_uses(), m_defs(), m_defs_sz(m_defs.size()),
        m_evalVisitor(*this) {}

  /// Create a SymStore. If globalParent is true, the created store has no
  /// parent.
  SymStore(ExprFactory &efac, bool trackUse = false, bool globalParent = false)
      : m_Parent(NULL), m_efac(efac), m_trackUse(trackUse), m_uses(), m_defs(),
        m_defs_sz(m_defs.size()), m_evalVisitor(*this) {
    if (!globalParent) {
      // -- create our own parent
      m_ownedParent = std::make_shared<SymStore>(efac, false, true);
      m_Parent = m_ownedParent.get();
    }
  }

  SymStore(const SymStore &other)
      : m_Parent(other.m_Parent), m_ownedParent(other.m_ownedParent),
        m_Store(other.m_Store), m_efac(other.m_efac),
        m_trackUse(other.m_trackUse), m_uses(other.m_uses),
        m_defs(other.m_defs), m_defs_sz(other.m_defs_sz),
        m_evalVisitor(*this) // create new m_evalVisitor
  {}

  SymStore &operator=(SymStore other) {
    this->swap(other);
    return *this;
  }

  void swap(SymStore &o);
  void print(llvm::raw_ostream &out);
  size_t size() { return m_Store.size(); }

  ExprFactory &getExprFactory() { return m_efac; }

  bool isDefined(Expr key) const { return m_Store.count(key) > 0; }

  Expr at(Expr key) const {
    if (isDefined(key))
      return m_Store.at(key);
    return Expr(0);
  }

  Expr eval(Expr exp) { return expr::dagVisit(m_evalVisitor, exp); }
  Expr operator()(Expr exp) { return eval(exp); }

  typedef ExprExprMap::iterator iterator;
  typedef ExprExprMap::const_iterator const_iterator;
  iterator begin() { return m_Store.begin(); }
  iterator end() { return m_Store.end(); }
  const_iterator begin() const { return m_Store.begin(); }
  const_iterator end() const { return m_Store.end(); }

  void clear() { reset(); }
  void reset() {
    m_Store.clear();
    m_uses.clear();
    m_defs.clear();
    m_defs_sz = 0;
    // if (m_ownedParent) m_ownedParent.reset (new SymStore (efac, false,
    // true));
    if (m_ownedParent)
      m_ownedParent->reset();
  }

  template <typename R> void uses(R &u) {
    m_uses.assign(std::begin(u), std::end(u));
  }
  const ExprVector &uses() const { return m_uses; }
  const ExprVector &defs();

  void write(Expr key, Expr val);
  Expr havoc(Expr key);
  Expr read(Expr key);
};

} // namespace seahorn

namespace std {
inline void swap(seahorn::SymStore &u, seahorn::SymStore &v) { u.swap(v); }
} // namespace std

#endif
