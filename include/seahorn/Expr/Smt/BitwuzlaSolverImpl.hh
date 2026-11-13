#ifdef WITH_BITWUZLA
#pragma once

#include "bitwuzla/cpp/bitwuzla.h"
#include "seahorn/Expr/Smt/MarshalBitwuzla.hh"
#include "seahorn/Expr/Smt/Solver.hh"

#include <cstdint>
#include <memory>
#include <string>
#include <unordered_set>

namespace llvm {
class raw_ostream;
}

namespace seahorn {
namespace solver {

/// \brief The Solver interface on top of Bitwuzla
///
/// add(), check(), reset() and get_model() are implemented so far. The other
/// methods print an error and exit, so that nothing mistakes them for a
/// real answer.
///
/// An assertion that cannot be encoded makes add() return false. Since
/// callers may ignore that (SolverBmc does), the solver also remembers it:
/// every check answers UNKNOWN until reset() removes it.
///
/// get_model() returns a bitwuzla_model_impl, which asks this solver for
/// values and is valid only until the next add(), check() or reset(). See
/// BitwuzlaModelImpl.hh. While an assertion has an equality between arrays
/// with indices narrower than 32 bits, or a quantifier, models have no
/// values.
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

  /** Clear all assertions */
  void reset() override;

  /// A model of the last check. If that check was not sat, or the solver
  /// changed since, logs an error and returns a model without values.
  model_ref get_model() override;

  /** Not supported yet */
  SolverResult check_with_assumptions(const expr_const_it_range &lits) override;
  void unsat_core(expr::ExprVector &out) override;
  void push() override;
  void pop() override;
  void to_smt_lib(llvm::raw_ostream &o) override;

private:
  friend class bitwuzla_model_impl;
  /// The value of \p e in the model of generation \p generation, or nondet
  expr::Expr eval_in_model(expr::Expr e, uint64_t generation);
  /// Prints the model of generation \p generation; see bitwuzla_model_impl
  void print_model(llvm::raw_ostream &o, uint64_t generation);

  bitwuzla::Options m_options;
  // -- declared before everything that holds terms, so destroyed last
  bitwuzla::TermManager m_tm;
  marshal_bitwuzla m_marshal;
  std::unique_ptr<bitwuzla::Bitwuzla> m_bzla;

  /// why an assertion could not be encoded; empty if every one was
  std::string m_unsupported;

  /// the assertions since the last reset, for printing a model
  expr::ExprVector m_assertions;

  /// An assertion since the last reset has an equality between arrays whose
  /// index is narrower than 32 bits. Bitwuzla may then give constants wrong
  /// values (see BitwuzlaSolverImpl.cc), so models give none.
  bool m_narrow_array_eq = false;
  /// the terms of the assertions already searched for such an equality
  std::unordered_set<bitwuzla::Term> m_scanned_assertions;

  /// An assertion since the last reset has a forall or an exists (perhaps
  /// from an equality with a function). Reading a value may then make
  /// Bitwuzla solve again (see BitwuzlaSolverImpl.cc), so models give none.
  bool m_quantified = false;
  /// the terms of the assertions already searched for a quantifier
  std::unordered_set<bitwuzla::Term> m_scanned_quantifiers;

  /// Increased by add(), check() and reset(), each of which ends the life of
  /// a model. It starts at 1, so the generation 0 is never current.
  uint64_t m_generation = 1;
  /// the generation of the last check that answered sat, 0 if none
  uint64_t m_sat_generation = 0;
  /// models hold a weak_ptr to this, so they know when the solver is gone
  std::shared_ptr<bitwuzla_solver_impl *> m_self;
};
} // namespace solver
} // namespace seahorn
#endif
