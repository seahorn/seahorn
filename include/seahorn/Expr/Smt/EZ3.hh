// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#pragma once
#include "seahorn/Expr/Smt/ExprToZ.hh"

namespace seahorn {
#ifdef SEA_REC_ZEXPR
using EZ3 = ZContext<ExprToZ, ZToExpr>;
#else
using EZ3 = ZContext<ExprToZ, ZToExprNoRec>;
#endif
}
