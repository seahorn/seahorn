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
/// operators, equality, and the bit-vector operators, including the overflow
/// predicates. Everything else throws UnsupportedExpr, among it int2bv,
/// bv2int, rotation by a term, and =>, <=>, = or distinct with other than
/// two arguments. Errors that Bitwuzla reports while encoding (such as a
/// width of 0) are thrown as UnsupportedExpr as well.
///
/// Results are cached, so encoding the same Expr twice returns the same
/// term, and every SeaHorn constant becomes exactly one Bitwuzla constant.
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
  bitwuzla::Term mkLeaf(expr::Expr e);
  bitwuzla::Term mkNode(expr::Expr e, const std::vector<bitwuzla::Term> &args);
  bitwuzla::Term declare(expr::Expr fdecl);

  bitwuzla::TermManager &m_tm;
  std::unordered_map<expr::Expr, bitwuzla::Term> m_cache;
};
} // namespace solver
} // namespace seahorn
#endif
