#pragma once

#include "seahorn/Expr/Expr.hh"

namespace seahorn {

namespace path_bmc {

void bool_abstraction(ExprVector &side, ExprVector &abs_side);

}
} // namespace seahorn
