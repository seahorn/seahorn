#ifdef WITH_BITWUZLA
#pragma once

#include "seahorn/Expr/Smt/Model.hh"

#include <cstdint>
#include <memory>

namespace llvm {
class raw_ostream;
}

namespace seahorn {
namespace solver {

class bitwuzla_solver_impl;

/// \brief A model of the last sat check of a bitwuzla_solver_impl
///
/// Unlike a Z3 model, which is a copy, this asks the solver for each value,
/// so it is only valid until the solver changes. It remembers the solver's
/// generation, which add(), check() and reset() increase. Once the solver has
/// changed, or is destroyed, eval() logs an error and returns nondet instead
/// of a value from some other model.
///
/// eval() returns true or false for a Bool term, the bit-vector numeral in
/// [0, 2^w) (the bits read as unsigned) for a bit-vector term of width w,
/// and store(... const-array(index sort, default) ...) of such numerals for
/// an array term. It returns nondet for any term it cannot evaluate: one the
/// encoder rejects, one of another sort, and one with an equality or
/// disequality between arrays inside, whose value Bitwuzla 0.9.1 can get
/// wrong. For the same reason it returns nondet for every term while an
/// assertion has such an equality over indices narrower than 32 bits. A
/// struct is evaluated field by field. Bitwuzla always completes its model,
/// so a constant in no assertion gets a value as well, and the \p complete
/// flag makes no difference.
class bitwuzla_model_impl : public Model {
public:
  /// \p generation 0 makes a model that never has values
  bitwuzla_model_impl(std::weak_ptr<bitwuzla_solver_impl *> solver,
                      uint64_t generation)
      : m_solver(std::move(solver)), m_generation(generation) {}

  expr::Expr eval(expr::Expr e, bool complete) override;

  /// Prints "constant = value" for every constant of the solver's assertions
  void print(llvm::raw_ostream &o) const override;

private:
  std::weak_ptr<bitwuzla_solver_impl *> m_solver;
  uint64_t m_generation;
};
} // namespace solver
} // namespace seahorn
#endif
