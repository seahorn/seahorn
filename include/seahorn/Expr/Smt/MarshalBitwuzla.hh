#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"
#include "seahorn/Expr/Expr.hh"

#include <stdexcept>
#include <string>
#include <unordered_map>
#include <vector>

namespace seahorn {
namespace solver {

/// \brief Thrown by marshal_bitwuzla for an Expr that it cannot encode
///
/// It holds the offending Expr, so it must be caught, and destroyed, while
/// that Expr's ExprFactory still exists.
class UnsupportedExpr : public std::runtime_error {
  expr::Expr m_expr;

public:
  UnsupportedExpr(expr::Expr e, const std::string &reason);
  /// \brief The offending sub-expression
  expr::Expr expr() const { return m_expr; }
};

/// \brief Encodes Exprs as Bitwuzla terms of a given TermManager
///
/// Supports Bool and bit-vector constants and numerals, the Boolean
/// operators, equality, the bit-vector operators, including the overflow
/// predicates, arrays from bit-vectors to bit-vectors (constants, select,
/// store, const-array), and the binders lambda, forall and exists over
/// bit-vector and Bool variables with their bound variables (de Bruijn
/// indices as in Z3: 0 is the last variable of the innermost binder).
///
/// A lambda is a Bitwuzla function, not an array as in Z3. So the
/// application of a term (fapp) is APPLY on a function and ARRAY_SELECT on
/// an array; select on a function is APPLY; store on a function is
/// (lambda x (ite (= x i) v (f x))); equality with a function on either side
/// is stated pointwise, (forall xs (= (a xs) (b xs))), because Bitwuzla has
/// no equality between functions; and an ite with a function in a branch is
/// moved inside a lambda, (lambda xs (ite c (t xs) (e xs))), because
/// Bitwuzla 0.9.1 aborts on an ite between lambdas.
///
/// Everything else throws UnsupportedExpr, among it int2bv, bv2int, rotation
/// by a term, =>, <=>, = or distinct with other than two arguments, other
/// array sorts, array-map, array-default, as-array, uninterpreted functions,
/// bound variables of other sorts, a bound variable outside its binder, and
/// a lambda whose body is a function (Bitwuzla would merge the two). Errors
/// that Bitwuzla reports while encoding (such as a width of 0) are thrown as
/// UnsupportedExpr as well.
///
/// Closed terms are cached, so encoding the same Expr twice returns the same
/// term, and every SeaHorn constant becomes exactly one Bitwuzla constant. A
/// term with a free bound variable means something else under another
/// binder, so it is cached only while its binder is being encoded.
///
/// Bitwuzla reports errors with C++ exceptions, so the files that use this
/// class are compiled with -fexceptions. No exception may escape into the
/// rest of SeaHorn, which may be compiled without them: callers catch
/// UnsupportedExpr (and bitwuzla::Exception) at their API boundary.
class marshal_bitwuzla {
public:
  explicit marshal_bitwuzla(bitwuzla::TermManager &tm) : m_tm(tm) {}

  /// \brief Encodes a term. Throws UnsupportedExpr.
  bitwuzla::Term encode_term(expr::Expr e);

  /// \brief Encodes a sort expression. Throws UnsupportedExpr.
  bitwuzla::Sort encode_sort(expr::Expr s);

private:
  /// A term, and one more than the largest de Bruijn index that is free in
  /// its Expr (0: the Expr is closed)
  struct Encoded {
    bitwuzla::Term term;
    unsigned fv;
  };
  /// The variables of a binder being encoded, and the terms built under it
  /// that have a free bound variable
  struct Scope {
    std::vector<bitwuzla::Term> vars;
    std::unordered_map<expr::Expr, Encoded> cache;
  };

  bool lookup(expr::Expr e, Encoded &out) const;
  void remember(expr::Expr e, const Encoded &enc);
  void enterBinder(expr::Expr e);
  Encoded leaveBinder(expr::Expr e);
  Encoded mkLeaf(expr::Expr e);
  Encoded mkBoundVar(expr::Expr e);
  bitwuzla::Term mkNode(expr::Expr e, const std::vector<bitwuzla::Term> &args);
  bitwuzla::Term declare(expr::Expr fdecl);

  /// A new variable for each argument of the function sort \p fun
  std::vector<bitwuzla::Term> freshVars(const bitwuzla::Sort &fun);
  bitwuzla::Term freshVar(const bitwuzla::Sort &s, const std::string &name);
  bitwuzla::Term mkApp(expr::Expr e, const bitwuzla::Term &f,
                       const std::vector<bitwuzla::Term> &args);
  bitwuzla::Term mkEq(expr::Expr e, bitwuzla::Kind k, const bitwuzla::Term &a,
                      const bitwuzla::Term &b);
  bitwuzla::Term mkIte(expr::Expr e, const bitwuzla::Term &c,
                       const bitwuzla::Term &t, const bitwuzla::Term &f);
  bitwuzla::Term mkStore(expr::Expr e, const bitwuzla::Term &a,
                         const bitwuzla::Term &i, const bitwuzla::Term &v);

  bitwuzla::TermManager &m_tm;
  /// closed terms
  std::unordered_map<expr::Expr, bitwuzla::Term> m_cache;
  /// the binders being encoded, innermost last
  std::vector<Scope> m_scopes;
  /// variables made so far, to give each a distinct name
  unsigned m_num_vars = 0;
};

/// \brief Decodes a value that Bitwuzla::get_value returned
///
/// A Bool value becomes true or false, and a bit-vector value of width w the
/// bit-vector numeral of width w whose number is in [0, 2^w) (the bits read
/// as unsigned). An array value, a chain of stores over a constant array,
/// becomes SeaHorn's store(... const-array(index sort, default) ...) with
/// the stores in the same order. Returns a null Expr for anything else: a
/// value of another sort, or a term that is not a value. Does not throw for
/// a non-null term.
expr::Expr decode_bitwuzla_value(const bitwuzla::Term &v,
                                 expr::ExprFactory &efac);
} // namespace solver
} // namespace seahorn
#endif
