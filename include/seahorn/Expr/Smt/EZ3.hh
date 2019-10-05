#pragma once
#include "seahorn/Expr/Smt/ExprToZ.hh"

namespace ufo {
using EZ3 = ufo::ZContext<seahorn::ExprToZ, seahorn::ZToExpr>;
}
