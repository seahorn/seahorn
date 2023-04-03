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

void updatePtrTCCache(const Expr &e, bool isPtr, PtrTypeCheckCache &cache);

/**
 * @brief recursively check whether e would resolve to an address
 *
 * @param e target Expr expression tree
 * @return true Any leaf contains BasePtr
 * @return false None of the leaves is BasePtr
 */
bool isPtrExpr(Expr e, PtrTypeCheckCache &c);

/**
 * @brief Return true if e is ptr with single base, either:
 * sea.obj_N or
 * bvadd(sea.obj_N, o...)
 * in which case set base := sea.obj_N and offset := o
 */
bool isSingleBasePtr(Expr e, size_t ptrWidth, Expr &base, Expr &offset);

/**
 * @brief given sea.obj_N, return N
 *
 * @param e should be a
 * @return int
 */
int getBasedAddrSerial(Expr e);

using PtrBitsZeroed = std::pair<Expr, size_t>;

/**
 * @brief if expr e is sematically zeroing out some bits @ end of a number
 *
 * @param e expression in question
 * @param pbz None if e is not zeroing out bits; (number, # of bits) otherwise
 * @return true e is zeroing out bit of a number
 * @return false e is zeroing out bit of a number
 */
bool isZeroBits(Expr e, PtrBitsZeroed &pbz);

} // end of namespace mem
} // end of namespace expr
