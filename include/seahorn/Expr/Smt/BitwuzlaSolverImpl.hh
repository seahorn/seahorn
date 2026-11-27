// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"
#include "seahorn/Expr/Smt/Solver.hh"

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_set>
#include <utility>
#include <vector>

namespace llvm {
class raw_ostream;
}

namespace seahorn {
namespace solver {

/// \brief The Solver interface on top of Bitwuzla
///
/// An assertion that cannot be encoded makes add() return false. Since
/// callers may ignore that (SolverBmc does), the solver also remembers it:
/// every check answers UNKNOWN until the pop() or reset() that removes it.
///
/// push() and pop() open and close scopes. pop() restores everything the
/// scope changed: its assertions, a failed add(), the model guards below.
/// A pop() with no scope open is an error: the caller's idea of the
/// assertions is lost, so every check answers UNKNOWN until reset().
///
/// check_with_assumptions() checks under assumptions, which must be Bool.
/// One that cannot be encoded, or is not Bool, makes that check UNKNOWN.
/// After an UNSAT check, unsat_core() gives the original assumption Exprs
/// that Bitwuzla found unsat with the assertions (empty after a plain
/// check()); at any other time it logs an error and gives nothing.
///
/// to_smt_lib() prints the assertions as they were added (see
/// BitwuzlaSmtLib.hh), never Bitwuzla's preprocessed formula. With an
/// assertion it could not encode, it prints only a comment saying so.
///
/// get_model() returns a bitwuzla_model_impl, which asks this solver for
/// values and is valid only until the next add(), check(),
/// check_with_assumptions(), push(), pop() or reset(); to_smt_lib() does
/// not end it. See BitwuzlaModelImpl.hh. While an assertion, or an
/// assumption of the last check, has an equality between arrays with
/// indices narrower than 32 bits, or a quantifier, models have no values.
///
/// Bitwuzla reports errors with exceptions. Every method catches them, so
/// none escapes into SeaHorn, which may be compiled without them.
class bitwuzla_solver_impl : public Solver {
public:
  using model_ref = typename Solver::model_ref;

  /// \p time_limit_ms, if not 0, limits each check; a check that runs out
  /// answers UNKNOWN. (Quantifiers can make Bitwuzla run for a long time.)
  explicit bitwuzla_solver_impl(uint64_t time_limit_ms = 0);
  ~bitwuzla_solver_impl() override;

  SolverKind get_kind() const override { return SolverKind::BITWUZLA; }

  bool add(expr::Expr exp) override;

  /** Check for satisfiability */
  SolverResult check() override;

  /** Check for satisfiability under the Bool assumptions \p lits */
  SolverResult check_with_assumptions(const expr_const_it_range &lits) override;

  /// The assumptions of the last check that Bitwuzla found unsat with the
  /// assertions, appended to \p out as the Exprs given, each once, in their
  /// order. Needs the last check to be UNSAT, with no change since.
  void unsat_core(expr::ExprVector &out) override;

  void push() override;
  void pop() override;

  /** Clear all assertions and scopes */
  void reset() override;

  /// A model of the last check. If that check was not sat, or the solver
  /// changed since, logs an error and returns a model without values.
  model_ref get_model() override;

  /** Write the assertions in SMT-LIB format */
  void to_smt_lib(llvm::raw_ostream &o) override;

private:
  friend class bitwuzla_model_impl;
  /// The value of \p e in the model of generation \p generation, or nondet
  expr::Expr eval_in_model(expr::Expr e, uint64_t generation);
  /// Prints the model of generation \p generation; see bitwuzla_model_impl
  void print_model(llvm::raw_ostream &o, uint64_t generation);
  /// Checks under \p assumptions (empty for check()), after the caller set
  /// m_assumptions and their guards
  SolverResult solve(const std::vector<bitwuzla::Term> &assumptions);
  /// Sets the model guards for \p t, which is asserted (or assumed, if
  /// \p assumed)
  void guard(const bitwuzla::Term &t, bool assumed);
  /// Ends the life of models and cores
  void changed() { ++m_generation; }
  /// The scope of each assertion of m_terms
  std::vector<size_t> levels() const;
  /// Turns on PRODUCE_UNSAT_ASSUMPTIONS until the next reset(): a new
  /// Bitwuzla instance with the assertions in their scopes (see
  /// BitwuzlaSolverImpl.cc)
  void enableCores();
  /// PRODUCE_UNSAT_ASSUMPTIONS is on
  bool m_cores = false;

  bitwuzla::Options m_options;
  // -- declared before everything that holds terms, so destroyed last
  bitwuzla::TermManager m_tm;
  marshal_bitwuzla m_marshal;
  std::unique_ptr<bitwuzla::Bitwuzla> m_bzla;

  /// why an assertion could not be encoded; empty if every one was. A pop()
  /// restores it.
  std::string m_unsupported;
  /// why the scopes are lost (a pop() with none open, or Bitwuzla failing
  /// to push or pop); empty if they are not. Only reset() clears it.
  std::string m_lost;

  /// the assertions since the last reset, for printing a model, and their
  /// terms, for to_smt_lib
  expr::ExprVector m_assertions;
  std::vector<bitwuzla::Term> m_terms;

  /// An assertion since the last reset has an equality between arrays whose
  /// index is narrower than 32 bits. Bitwuzla may then give constants wrong
  /// values (see BitwuzlaSolverImpl.cc), so models give none.
  bool m_narrow_array_eq = false;
  /// terms known to have no such equality inside
  std::unordered_set<bitwuzla::Term> m_no_array_eq;

  /// An assertion since the last reset has a forall or an exists (perhaps
  /// from an equality with a function). Reading a value may then make
  /// Bitwuzla solve again (see BitwuzlaSolverImpl.cc), so models give none.
  bool m_quantified = false;
  /// terms known to have no quantifier inside
  std::unordered_set<bitwuzla::Term> m_no_quantifier;

  /// What pop() restores, saved by push()
  struct Scope {
    size_t num_assertions;
    std::string unsupported;
    bool narrow_array_eq;
    bool quantified;
  };
  std::vector<Scope> m_scopes;

  /// the assumptions of the last check, each once, in the order given, with
  /// their terms; empty after check()
  std::vector<std::pair<bitwuzla::Term, expr::Expr>> m_assumptions;
  /// an assumption of the last check has what the two guards above look for
  bool m_assumed_narrow_array_eq = false;
  bool m_assumed_quantified = false;

  /// Increased by add(), check(), check_with_assumptions(), push(), pop()
  /// and reset(), each of which ends the life of a model and a core. It starts
  /// at 1, so the generation 0 is never current.
  uint64_t m_generation = 1;
  /// the generation of the last check that answered sat, 0 if none
  uint64_t m_sat_generation = 0;
  /// the generation of the last check that answered unsat, 0 if none
  uint64_t m_unsat_generation = 0;
  /// models hold a weak_ptr to this, so they know when the solver is gone
  std::shared_ptr<bitwuzla_solver_impl *> m_self;
};
} // namespace solver
} // namespace seahorn
#endif
