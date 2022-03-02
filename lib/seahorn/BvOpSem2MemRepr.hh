#pragma once

#include "BvOpSem2RawMemMgr.hh"
#include "seahorn/Expr/ExprAddrRangeMap.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

namespace seahorn {
namespace details {

/// \Brief Base class for memory representation
class OpSemMemRepr {
protected:
  RawMemManagerCore &m_memManager;
  Bv2OpSemContext &m_ctx;
  ExprFactory &m_efac;
  static constexpr unsigned m_BitsPerByte = 8;

public:
  using PtrTy = RawMemManagerCore::PtrTy;
  using PtrSortTy = RawMemManagerCore::PtrSortTy;
  using MemValTy = RawMemManagerCore::MemValTy;

  OpSemMemRepr(RawMemManagerCore &memManager, Bv2OpSemContext &ctx)
      : m_memManager(memManager), m_ctx(ctx), m_efac(ctx.getExprFactory()) {}
  virtual ~OpSemMemRepr() = default;

  virtual Expr coerce(Expr sort, Expr val) = 0;
  virtual Expr loadAlignedWordFromMem(PtrTy ptr, MemValTy mem) = 0;
  virtual MemValTy storeAlignedWordToMem(Expr val, PtrTy ptr, PtrSortTy ptrSort,
                                         MemValTy mem) = 0;

  virtual MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                          unsigned wordSzInBytes, PtrSortTy ptrSort,
                          uint32_t align) = 0;
  virtual MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                          unsigned wordSzInBytes, PtrSortTy ptrSort,
                          uint32_t align) = 0;
  virtual MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len,
                          MemValTy memTrsfrRead, MemValTy memRead,
                          unsigned wordSzInBytes, PtrSortTy ptrSort,
                          uint32_t align) = 0;
  virtual MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len,
                          MemValTy memTrsfrRead, MemValTy memRead,
                          unsigned wordSzInBytes, PtrSortTy ptrSort,
                          uint32_t align) = 0;

  virtual MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                           unsigned wordSzInBytes, PtrSortTy ptrSort,
                           uint32_t align) = 0;
  virtual MemValTy FilledMemory(PtrSortTy ptrSort, Expr val) = 0;
};

/// \brief Represent memory regions by logical arrays
class OpSemMemArrayReprBase : public OpSemMemRepr {
public:
  OpSemMemArrayReprBase(RawMemManagerCore &memManager, Bv2OpSemContext &ctx,
                        unsigned memCpyUnrollCnt)
      : OpSemMemRepr(memManager, ctx), m_memCpyUnrollCnt(memCpyUnrollCnt) {}

  Expr coerce(Expr _, Expr val) override { return val; }

  MemValTy storeAlignedWordToMem(Expr val, PtrTy ptr, PtrSortTy ptrSort,
                                 MemValTy mem) override {
    (void)ptrSort;
    return MemValTy(op::array::store(mem.toExpr(), ptr.toExpr(), val));
  }

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                  unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                  unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, MemValTy memTrsfrRead,
                  MemValTy memRead, unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                   unsigned wordSzInBytes, PtrSortTy ptrSort,
                   uint32_t align) override;
  MemValTy FilledMemory(PtrSortTy ptrSort, Expr val) override {
    return MemValTy(op::array::constArray(ptrSort.toExpr(), val));
  }

private:
  unsigned m_memCpyUnrollCnt;
};

/// \brief default un-optmized array mem repr
class OpSemMemArrayRepr : public OpSemMemArrayReprBase {
public:
  OpSemMemArrayRepr(RawMemManagerCore &memManager, Bv2OpSemContext &ctx,
                    unsigned memCpyUnrollCnt)
      : OpSemMemArrayReprBase(memManager, ctx, memCpyUnrollCnt) {}

  /** load(mem, ptr) -> select(mem, ptr) **/
  Expr loadAlignedWordFromMem(PtrTy ptr, MemValTy mem) override {
    return op::array::select(mem.toExpr(), ptr.toExpr());
  }
};

/// \brief Represent memory regions by:
/// store: array
/// load: optimized ITE
class OpSemMemHybridRepr : public OpSemMemArrayReprBase {
public:
  OpSemMemHybridRepr(RawMemManagerCore &memManager, Bv2OpSemContext &ctx,
                     unsigned memCpyUnrollCnt)
      : OpSemMemArrayReprBase(memManager, ctx, memCpyUnrollCnt),
        m_memCache(DagVisitMemCache()), m_cache(DagVisitCache()) {}

  /**
   * mem: 1. array const i.e. A (uninitialized)
   *      2. store expr i.e. store(mem, idx, val)
   *      3. ITE of array expr i.e. ite(cond, mem1, mem2)
   * MemValTy = ArrayConst A | Store A id val | ITE cond mem1 mem2
   * match mem with
   *      ArrayConst A -> { return select(A, ptr) (A[ptr]) }
   *      Store A idx val -> { return ite( (idx == ptr), val, A[ptr] )}
   *      ITE cond mem1 mem2 -> { return ite(cond, mem1[ptr], mem2[ptr]) }
   * **/
  Expr loadAlignedWordFromMem(PtrTy ptr, MemValTy mem) override;

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                  unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                  unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, MemValTy memTrsfrRead,
                  MemValTy memRead, unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;

private:
  DagVisitMemCache m_memCache;
  DagVisitCache m_cache;

  /**
   * @brief Create Hybrid repr expressions for read/select (a word) from
   * [arr] at [idx]
   * @param arr Memory (ME) being read from
   * @param idx Pointer (PE) to access
   * @param arm AddrRangeMap simplifying away some stores
   * @return Expr
   */
  Expr createHybridReadWord(Expr arr, Expr idx,
                            expr::addrRangeMap::AddrRangeMap &arm);
};

/// \brief Represent memory regions by lambda functions
class OpSemMemLambdaRepr : public OpSemMemRepr {
public:
  OpSemMemLambdaRepr(RawMemManagerCore &memManager, Bv2OpSemContext &ctx)
      : OpSemMemRepr(memManager, ctx) {}

  Expr coerce(Expr sort, Expr val) override {
    return isOp<ARRAY_TY>(sort) ? coerceArrayToLambda(val) : val;
  }

  Expr loadAlignedWordFromMem(PtrTy ptr, MemValTy mem) override {
    return bind::fapp(mem.toExpr(), ptr.toExpr());
  }

  MemValTy storeAlignedWordToMem(Expr val, PtrTy ptr, PtrSortTy ptrSort,
                                 MemValTy mem) override;
  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                  unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                  unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, MemValTy memTrsfrRead,
                  MemValTy memRead, unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, unsigned wordSzInBytes, PtrSortTy ptrSort,
                  uint32_t align) override;
  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                   unsigned wordSzInBytes, PtrSortTy ptrSort,
                   uint32_t align) override;
  MemValTy FilledMemory(PtrSortTy ptrSort, Expr v) override;

private:
  Expr coerceArrayToLambda(Expr arrVal);
  Expr makeLinearITE(PtrTy addr, const std::vector<PtrTy> &ptrKeys,
                     const ExprVector &vals, Expr fallback);
  // address of the last word that is copied into dst
  MemValTy createMemCpyExpr(const PtrTy &dPtr, const PtrTy &sPtr,
                            const MemValTy &memRead, const PtrSortTy &ptrSort,
                            const MemValTy &srcMem, const PtrTy &dstLast,
                            unsigned wordSzInBytes, uint32_t align) const;
};

} // namespace details
} // namespace seahorn
