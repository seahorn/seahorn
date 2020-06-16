#pragma once
#include "seahorn/Expr/ExprCore.hh"
#include "seahorn/Expr/ExprOpSort.hh"

namespace expr {

class TypeChecker;

class TypeCheckerHelper {
  friend class TypeChecker;

  class Impl;
  Impl *m_impl;

  TypeCheckerHelper();
  ~TypeCheckerHelper();

public:

  Expr typeOf(Expr e);
  Expr getErrorExp();

  void mapBoundVar(Expr bVar);
  ExprSet getBoundVars(Expr exp);
};

class TypeChecker {
  TypeCheckerHelper m_helper;

public:
  TypeChecker();

  /*
  See typeOf(Expr e);
  */
  Expr sortOf(Expr e) { return this->typeOf(e); }

  /*
  Returns the type of the passed expression. If an error is found (ie. the
  expression is not well-formed) in any subexpression, it will
  return an expression of type ERROR_TY. To get the error, call getErrorExp()
  */
  Expr typeOf(Expr e);

  /*
 - To be called after sortOf() or typeOf().
 - Returns the expression that is not well-formed if an error was found,
  otherwise it returns nullptr.
  - The error expression is reset everytime sorOf() or typeOf() is called
  */
  Expr getErrorExp();
};

} // namespace expr
