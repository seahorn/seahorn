#pragma once
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpSort.hh"

namespace expr {

/**
 * \class TypeChecker checks if an expression is well-formed and finds the type
 * of the expression
 *
 * Adding new operators (general): Override the Operator class's inferType
 * method. It should return the type of the specific operator
 *
 * Adding new Normal operators (NOP, DefOp): The type checking is defined
 * externally. Create a struct that inherits TypeCheckBase (in TypeCheckBase.hh)
 * with an inferType(Expr, TypeChecker&) function and pass this struct to
 * NOP/DefOp
 *
 * Adding new Terminal operators: The type checking is defined internally. Every
 * terminal trait defines its own inferType(Expr, TypeChecker&) function
 *
 */
class TypeChecker {
  class Impl;
  Impl *m_impl;

public:
  TypeChecker();
  ~TypeChecker();

  /**
   * \see typeOf(Expr e);
   */
  Expr sortOf(Expr e) { return this->typeOf(e); }

  /**
   * Finds the type of the passed expression
   *
   * \param e the expression that you wish to get the type of
   *
   * \return the type of the passed expression. ERROR_TY if it is an error
   *
   * \note if an error is found, call getErrorExp() to get it
   */
  Expr typeOf(Expr e);

  /**
   * \return the error expression if it is not well-formed, nullptr if it is
   * well-formed
   *
   * \note should be called after typeOf() or sortOf()
   * \note the error expression is reset everytime sortOf() or typeOf() is
   * called
   * \note only stores the first error that it finds (ie. the
   * leftmost, bottom-most error)
   */
  Expr getErrorExp();
};

} // namespace expr
