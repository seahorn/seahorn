#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"

#include <cstddef>
#include <string>
#include <vector>

namespace seahorn {
namespace solver {

/// \brief \p terms with every application of a lambda beta-reduced
///
/// An application (f a1 ... an) of a lambda of n variables (Bitwuzla nests
/// them, a lambda of a lambda) becomes the lambda's body with each variable
/// replaced by its argument, and so on inside it. The results mean the same
/// as \p terms. A lambda that is not applied stays. Works without recursion
/// (formulas can be deep), and replaces a variable only inside the subterms
/// where it is free, so a chain of n stores costs n steps per address.
/// Throws bitwuzla::Exception on error.
std::vector<bitwuzla::Term>
betaReduce(bitwuzla::TermManager &tm, const std::vector<bitwuzla::Term> &terms);

/// \brief An SMT-LIB script that asserts \p assertions, for the standalone
/// bitwuzla and z3
///
/// \p assertions[i] belongs to scope \p levels[i] (0 is outside every push;
/// the levels do not decrease), and the script pushes before each deeper
/// scope. It starts with (set-logic ALL) and ends with (check-sat) and
/// (exit). The terms are printed as given, never Bitwuzla's preprocessed
/// formula, after these steps:
/// - every application of a lambda is beta-reduced (betaReduce), since
///   Bitwuzla 0.9.1's parser cannot read lambda;
/// - a constant or variable whose name is missing, taken by an earlier one,
///   cannot be printed (| or \), would be read as something else (a leading
///   digit), is one of Bitwuzla's own names (@bzla., _let) or a name its
///   parser reserves (every token of its symbol table), is renamed to
///   name!N, a name used nowhere else;
/// - every closed term that is not a leaf and is used twice or more gets a
///   (define-const def!N ...) at the top, children first, and the rest is
///   printed over those names. So the text grows with the formula's DAG,
///   inside binders too. Bitwuzla's lets stay on, except in a term with a
///   binder inside another binder's body (its lets could leave their
///   scope there, plan 1.7).
///
/// Sets \p lambda_left, if given, when a lambda that is not applied is left
/// (Bitwuzla's parser cannot read the script then; z3 can). Throws
/// bitwuzla::Exception or std::runtime_error on error.
std::string printSmtLib(bitwuzla::TermManager &tm,
                        const std::vector<bitwuzla::Term> &assertions,
                        const std::vector<size_t> &levels,
                        bool *lambda_left = nullptr);

} // namespace solver
} // namespace seahorn
#endif
