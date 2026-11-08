// SPDX-FileCopyrightText: 2026 The SeaHorn Authors
// SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

#pragma once

#include "seahorn/Expr/Expr.hh"

namespace seahorn {

namespace path_bmc {

void boolAbstraction(ExprVector &side, ExprVector &abs_side);

}
} // namespace seahorn
