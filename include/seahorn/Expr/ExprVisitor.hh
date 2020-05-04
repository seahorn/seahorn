/// Expr Visitor
#pragma once

#include "seahorn/Expr/ExprCore.hh"
#include "llvm/Support/ErrorHandling.h"
#include <unordered_map>

namespace expr {
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
  using fn_type = std::shared_ptr<T>;

  fn_type fn;

  ExprFunctionoid(T *f) : fn_type(fn) {}
  ExprFunctionoid(fn_type f) : fn(f) {}
  Expr apply(Expr e) { return (*fn)(e); }
};
} // namespace

class VisitAction {
protected:
  bool m_skipKids;
  Expr m_expr;

private:
  std::shared_ptr<ExprFn> m_fn;

public:
  // skipKids or doKids
  VisitAction(bool kids = false)
      : m_skipKids(kids), m_fn(new ExprFunctionoid<IdentityRewriter>(
                             std::make_shared<IdentityRewriter>())) {}

  // changeTo or doKidsRewrite
  template <typename R>
  VisitAction(Expr e, bool kids = false,
              std::shared_ptr<R> r = std::make_shared<IdentityRewriter>())
      : m_skipKids(kids), m_expr(e), m_fn(new ExprFunctionoid<R>(r)) {}

  bool isSkipKids() { return m_skipKids && m_expr.get() == nullptr; }
  bool isChangeTo() { return m_skipKids && m_expr.get() != nullptr; }
  bool isDoKids() { return !m_skipKids && m_expr.get() == nullptr; }
  bool isChangeDoKidsRewrite() { return !m_skipKids && m_expr.get() != nullptr; }

  Expr rewrite(Expr v) { return m_fn->apply(v); }

  Expr getExpr() { return m_expr; }

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

};

using DagVisitCache = std::unordered_map<ENode *, Expr>;

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

      for (auto b = res->args_begin(), e = res->args_end(); b != e; ++b) {
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

  for (auto b = res->args_begin(), e = res->args_end(); b != e; ++b) {
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
} // namespace expr

// useful visitors
namespace expr {
namespace {
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

/** Applies a rewriter */
template <typename T> Expr rewrite(std::shared_ptr<T> r, Expr e) {
  RW<T> rw(r);
  return dagVisit(rw, e);
}

namespace {

template <typename F, typename OutputIterator>
struct FV : public std::unary_function<Expr, VisitAction> {
  F filter;

  OutputIterator out;
  ExprSet seen;

  typedef FV<F, OutputIterator> this_type;
  FV(const this_type &o) : filter(o.filter), out(o.out), seen(o.seen) {
    llvm_unreachable(nullptr);
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
} // namespace
// -- collect all sub-expressions of exp that satisfy the filter
template <typename F, typename OutputIterator>
void filter(Expr exp, F filter, OutputIterator out) {
  FV<F, OutputIterator> fv(filter, out);
  dagVisit(fv, exp);
}

namespace {
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

} // namespace
template <typename F> fn_map<F> mk_fn_map(const F &fn) { return fn_map<F>(fn); }

template <typename M> Expr replace(Expr exp, const M &map) {
  RV<M> rv(map);
  return dagVisit(rv, exp);
}

} // namespace expr
