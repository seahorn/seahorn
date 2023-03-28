#pragma once
#include "seahorn/Expr/Smt/ExprToZ.hh"

namespace seahorn {
#ifdef SEA_REC_ZEXPR
using EZ3 = ZContext<ExprToZ, ZToExpr>;
#else
using EZ3 = ZContext<ExprToZ, ZToExprNoRec>;
#endif
}
