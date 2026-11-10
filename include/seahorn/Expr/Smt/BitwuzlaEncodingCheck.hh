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
/// between the two encodings. Never throws.
EncodingCheck checkBitwuzlaEncoding(expr::Expr e, const bitwuzla::Term &t,
                                    unsigned timeout_ms);

} // namespace solver
} // namespace seahorn
#endif
