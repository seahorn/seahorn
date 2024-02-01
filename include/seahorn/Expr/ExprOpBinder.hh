/// bound variables, quantifiers, and lambdas
#pragma once

#include "seahorn/Expr/ExprApi.hh"
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpBind.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprVisitor.hh"
#include "seahorn/Expr/TypeCheckerUtils.hh"

#include <array>
#include <deque>

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

  static TerminalKind getKind() { return TerminalKind::BVAR; }
  static std::string name() { return "bind::BoundVar"; }
  static inline Expr inferType(Expr exp, TypeChecker &tc) {
    return sort::bvarTerminalTy(exp->efac());
  }
};

namespace op {
using BVAR = Terminal<bind::BoundVar>;

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

namespace typeCheck {
namespace bindType {

static inline bool binderCheck(Expr exp, TypeChecker &tc,
                               ExprVector &boundTypes) {
  if (exp->arity() == 0)
    return false;

  // makes sure that all of the binders arguments are constants and store their
  // types
  for (auto b = exp->args_begin(), e = exp->args_end() - 1; b != e; b++) {
    if (!bind::IsConstDecl()(*b))
      return false;

    Expr type = tc.typeOf(*b);
    boundTypes.push_back(type);
  }

  return true;
}

struct Lambda : public TypeCheckBase{
  /// ensures that all children except for the last (the body) are constants
  /// \note does not check bound variables
  /// \return FUNCTIONAL_TY
  /// for example, for the expression lambda a, b, c ... :: body, the return
  /// type is FUNCTIONAL_TY(typeOf(a), typeOf(b), ... , typeOf(body))
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    ExprVector boundTypes;
    if (!binderCheck(exp, tc, boundTypes))
      return sort::errorTy(exp->efac());

    Expr body = exp->last();
    boundTypes.push_back(tc.typeOf(body));

    return mknary<FUNCTIONAL_TY>(boundTypes);
  }
};

struct Quantifier : public TypeCheckBase{
  /// ensures that: 1. all children except for the last (the body) are constants
  ///  2. the body type is BOOL_TY
  /// \note does not check bound variables
  /// \return BOOL_TY
  inline Expr inferType(Expr exp, TypeChecker &tc) override {
    ExprVector boundTypes;
    Expr body = exp->last();
    if (!(binderCheck(exp, tc, boundTypes) &&
          isOp<BOOL_TY>(tc.typeOf(body))))
      return sort::errorTy(exp->efac());

    return sort::boolTy(exp->efac());
  }
};
} // namespace bindType
} // namespace typeCheck

enum class BinderOpKind { FORALL, EXISTS, LAMBDA };
NOP_BASE(BinderOp)
/** Forall quantifier */
NOP(FORALL, "forall", bind::BINDER, BinderOp, typeCheck::bindType::Quantifier)
/** Exists */
NOP(EXISTS, "exists", bind::BINDER, BinderOp, typeCheck::bindType::Quantifier)
/** Lambda */
NOP(LAMBDA, "lambda", bind::BINDER, BinderOp, typeCheck::bindType::Lambda)

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

inline Expr push_ite_lambda(Expr c, Expr lhs, Expr rhs) {
  assert(isOpX<LAMBDA>(lhs));
  assert(isOpX<LAMBDA>(rhs));
  // (ite (lambda ( x ) lhs) (lambda ( x ) rhs))
  ///                      ==
  // (lambda ( y ) (ite c ((lambda ( x ) lhs) y) ((lambda ( x ) rhs) y)))

  // pick one lambda term to extract abstracted terms
  Expr lambda = isOpX<LAMBDA>(lhs) ? lhs : rhs;

  // -- save abstracted term
  ExprVector args;
  args.reserve(lambda->arity());
  for (unsigned i = 0, sz = bind::numBound(lambda); i < sz; ++i) {
    args.push_back(bind::decl(lambda, i));
  }

  // -- create corresponding bound variables
  ExprVector vars;
  vars.reserve(lambda->arity());
  // -- reserve a place for lambda
  vars.push_back(Expr());

  for (unsigned i = 0, sz = bind::numBound(lambda); i < sz; ++i)
    vars.push_back(bind::bvar(i, bind::boundSort(lambda, i)));

  // -- turn lhs into an application
  vars[0] = lhs;
  Expr _lhs = mknary<FAPP>(vars);

  // -- turn rhs into an application
  vars[0] = rhs;
  Expr _rhs = mknary<FAPP>(vars);

  // -- add body of new lambda
  args.push_back(mk<ITE>(c, _lhs, _rhs));

  // -- create lambda
  return mknary<LAMBDA>(args);
}

/// \Brief create ite with lambda aware simplifications
inline Expr lite(Expr c, Expr lhs, Expr rhs) {
  if (isOpX<TRUE>(c))
    return lhs;
  if (isOpX<FALSE>(c))
    return rhs;
  if (lhs == rhs)
    return lhs;

  if (isOpX<LAMBDA>(lhs) && isOpX<LAMBDA>(rhs)) {
    return push_ite_lambda(c, lhs, rhs);
  }
  return mk<ITE>(c, lhs, rhs);
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
} // namespace expr

namespace expr {
namespace details {
template <typename Abs> struct ABSCST;

template <typename Range> struct AbsCst {
  typedef AbsCst<Range> this_type;

  const Range &m_r;
  std::unordered_map<Expr, unsigned> m_evmap;

  std::deque<ABSCST<this_type>> m_pinned;

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
