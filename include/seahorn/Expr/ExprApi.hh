/// Public API for constructing expressions
#pragma once

namespace expr {

/**********************************************************************/
/* Inspection */
/**********************************************************************/

// -- usage isOp<TYPE>(EXPR) . Returns true if top operator of
// -- expression is a subclass of TYPE.
template <typename O, typename T> bool isOp(T e) {
  return llvm::isa<O>(&eptr(e)->op());
}

// -- usage isOpX<TYPE>(EXPR) . Returns true if top operator of
// -- expression is of type TYPE.
template <typename O, typename T> bool isOpX(T e) { return isOp<O>(e); }

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
  using term_type = Terminal<T>;
  assert(llvm::isa<term_type>(e->op()));
  return llvm::dyn_cast<const term_type>(&e->op())->get();
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
  return mknary<T>(std::begin(r), std::end(r));
}

template <typename T, typename Range> Expr mknary(Expr base, const Range &r) {
  return mknary<T>(base, std::begin(r), std::end(r));
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

} // namespace expr
