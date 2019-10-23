/// Expr Visitor
#pragma once

#include "seahorn/Expr/ExprCore.hh"

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

  bool isSkipKids() { return _skipKids && expr.get() == nullptr; }
  bool isChangeTo() { return _skipKids && expr.get() != nullptr; }
  bool isDoKids() { return !_skipKids && expr.get() == nullptr; }
  bool isChangeDoKidsRewrite() { return !_skipKids && expr.get() != nullptr; }

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
