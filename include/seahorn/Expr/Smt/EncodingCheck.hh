#pragma once

#include "seahorn/Expr/Expr.hh"

#include <string>
#include <vector>

namespace seahorn {
namespace solver {

/// \brief The outcome of comparing another solver's term with Z3's encoding
enum class EncodingVerdict {
  /// Z3 proved that the two are equal
  SAME,
  /// Z3 found values of the constants on which they differ, or their sorts
  /// differ
  DIFFERENT,
  /// Z3 gave up (time limit)
  UNDECIDED,
  /// the comparison could not be set up (see the detail)
  UNCHECKED
};

const char *verdictName(EncodingVerdict v);

struct EncodingCheck {
  EncodingVerdict verdict;
  /// why UNDECIDED or UNCHECKED, or for DIFFERENT the differing values
  std::string detail;
};

/// \brief A free constant of an SMT-LIB term: Bool if \p bv_width is 0, a
/// bit-vector otherwise. If \p index_width is not 0, it is an array from
/// bit-vectors of that width to that sort.
struct SmtLibConst {
  std::string name;
  unsigned bv_width;
  unsigned index_width = 0;
};

/// \brief Checks with Z3 that the SMT-LIB term \p term equals Z3's
/// encoding of \p e
///
/// Translation validation for another solver's encoder. That solver prints
/// its encoding of \p e as \p term, an SMT-LIB term over the constants
/// \p consts and of sort \p term_bv_width (0 for Bool). Z3 parses it and
/// proves it equal to SeaHorn's own Z3 encoding of \p e, within
/// \p timeout_ms milliseconds. Constants are matched by name: both encoders
/// name a constant after its declaration.
///
/// Uses only Z3's C API with explicit error checks, so it behaves the same
/// whether or not SeaHorn is compiled with exceptions.
///
/// If \p quantified (the term has a quantifier or an equality with a
/// function), a difference that Z3 finds is reported UNDECIDED: Z3 5.1.0 has
/// answered sat, and even evaluated its values, wrongly on equalities with
/// lambdas. A proof that the two are equal is still SAME.
EncodingCheck checkSmtLibTermWithZ3(expr::Expr e, const std::string &term,
                                    const std::vector<SmtLibConst> &consts,
                                    unsigned term_bv_width, unsigned timeout_ms,
                                    bool quantified = false);

} // namespace solver
} // namespace seahorn
