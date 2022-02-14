#pragma once
#include "seahorn/Expr/ExprAddrRangeMap.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

/** Util functions and visitors for Expr trees representing memory **/

namespace expr {
using namespace addrRangeMap;
namespace mem {
/** Adhoc heuristic: Returns true if e is either:
 * bvnum larger than 0xbf000000, or
 * terminal string starting with sea.sp0;
 * With `BasedPtrObj` on: match "sea.obj_n" objects
 **/
bool isBaseAddr(Expr e);

/**
 * @brief recursively check whether e would resolve to an address
 *
 * @param e target Expr expression tree
 * @return true Any leaf contains BasePtr
 * @return false None of the leaves is BasePtr
 */
bool isPtrExpr(Expr e);

/**
 * @brief Given a ptr expression pE, build MemAddrRangeMap according to
 * type of pE:
 * - base addr: {pE => (0, 0)}
 * - bvadd(x, y): addrRangeMapOf(x) + addrRangeMapOf(y)
 * - ITE(c, x, y): addrRangeMapOf(x) | addrRangeMapOf(y), replace collidding
 * elements with larger range
 */
AddrRangeMap addrRangeMapOf(Expr pE);

/**
 * @brief Given a num expression nE, build AddrRange according to
 * type of nE:
 * - num(n): {nE => (n, n)}
 * - sym(x): {nE => any} XXX: could use contextual infer
 * - bvadd(x, y): addrRangeOf(x) + addrRangeOf(y)
 * - ITE(c, x, y): addrRangeOf(x).join(addrRangeOf(y))
 */
AddrRange addrRangeOf(Expr nE);

using PtrBitsZeroed = std::pair<Expr, size_t>;

bool isZeroBits(Expr e, PtrBitsZeroed &pbz);

} // end of namespace mem
} // end of namespace expr