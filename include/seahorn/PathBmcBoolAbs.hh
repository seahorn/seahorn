#pragma once

#include "seahorn/Expr/Expr.hh"

namespace seahorn {

namespace path_bmc {

void boolAbstraction(ExprVector &side, ExprVector &abs_side);

}
} // namespace seahorn
