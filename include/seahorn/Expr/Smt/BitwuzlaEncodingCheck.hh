#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"
#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/Smt/EncodingCheck.hh"

namespace seahorn {
namespace solver {

/// \brief Checks with Z3 that the Bitwuzla term \p t means the same as
/// Z3's encoding of \p e
///
/// Translation validation for marshal_bitwuzla. Bitwuzla prints \p t in
/// SMT-LIB, and checkSmtLibTermWithZ3 has Z3 parse it and compare it with
/// SeaHorn's Z3 encoding of \p e. So no code of the Bitwuzla adapter stands
/// between the two encodings.
///
/// Bitwuzla 0.9.1 prints a term with binders (lambda, forall, exists)
/// wrongly when a subterm is shared inside and outside a binder: its let
/// names leave their scope. For such a term, every closed subterm gets a let
/// of its own at the top, which Bitwuzla prints with no let, over the
/// names of its closed subterms; this needs \p tm, the term's
/// TermManager, and without it the term is UNCHECKED. Never throws.
EncodingCheck checkBitwuzlaEncoding(expr::Expr e, const bitwuzla::Term &t,
                                    unsigned timeout_ms,
                                    bitwuzla::TermManager *tm = nullptr);

} // namespace solver
} // namespace seahorn
#endif
