#pragma once
#include "ZExprConverter.hh"
#include "seahorn/Expr/Smt/ExprToZ.hh"

namespace ufo {
typedef ::ufo::ZContext<seahorn::ExprToZ, BasicExprUnmarshal<FailUnmarshal>> EZ3;
}
