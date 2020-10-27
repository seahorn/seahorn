#pragma once

#include "BvOpSem2Context.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "seahorn/Expr/ExprOpStruct.hh"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"

#include "llvm/Support/MathExtras.h"
#include <cstdint>

namespace seahorn {
namespace details {

// This memory manager adds a metadata memory(backed by raw memory) sitting side
// by side to conventional memory(backed by raw memory). The word size for
// conventional memory can be greater than metadata memory.
//
// Currently this implementation has a metadata memory word size of 1 byte.
// For every byte written to conventional memory, we set the corresponding
// metadata memory address to value 1.
class TrackingRawMemManager : public OpSemMemManagerBase {
private:
  RawMemManager m_main;
  RawMemManager m_metadata;

  static const unsigned int g_MetadataBitWidth = 8;
  static const unsigned int g_MetadataByteWidth = g_MetadataBitWidth / 8;
  static const unsigned int g_num_slots = 2;

public:
  using PtrTy = OpSemMemManager::PtrTy;
  using PtrSortTy = OpSemMemManager::PtrSortTy;
  using MemRegTy = OpSemMemManager::MemRegTy;
  using RawMemValTy = OpSemMemManager::MemValTy;
  using RawMemSortTy = OpSemMemManager::MemSortTy;

  struct MemValTyImpl {
    Expr m_v;

    MemValTyImpl(RawMemValTy &&raw_val, Expr &&metadata_val) {
      assert(!strct::isStructVal(raw_val));
      assert(!strct::isStructVal(metadata_val));
      m_v = strct::mk(std::move(raw_val), std::move(metadata_val));
    }

    MemValTyImpl(const RawMemValTy &raw_val, const RawMemValTy &metadata_val) {
      assert(!strct::isStructVal(raw_val));
      assert(!strct::isStructVal(metadata_val));
      m_v = strct::mk(raw_val, metadata_val);
    }

    explicit MemValTyImpl(const Expr &e) {
      // Our base is a struct of two exprs
      assert(strct::isStructVal(e));
      assert(!strct::isStructVal(e->arg(0)));
      assert(!strct::isStructVal(e->arg(1)));
      assert(e->arity() == g_num_slots);
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawMemValTy getRaw() { return strct::extractVal(m_v, 0); }

    Expr getMetadata() { return strct::extractVal(m_v, 1); }
  };

  struct MemSortTyImpl {
    Expr m_mem_sort;

    MemSortTyImpl(RawMemSortTy &&mem_sort, Expr &&metadata_sort) {
      m_mem_sort =
          sort::structTy(std::move(mem_sort), std::move(metadata_sort));
    }

    MemSortTyImpl(const RawMemSortTy &mem_sort, Expr &metadata_sort) {
      m_mem_sort = sort::structTy(mem_sort, metadata_sort);
    }
    Expr v() const { return m_mem_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }
  };

  using MemValTy = MemValTyImpl;
  using MemSortTy = MemSortTyImpl;

  TrackingRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                        unsigned wordSz, bool useLambdas);

  TrackingRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                        unsigned wordSz, bool useLambdas, bool ignoreAlignment);

  ~TrackingRawMemManager() = default;

  OpSemAllocator &getMAllocator() const { return m_main.getMAllocator(); }

  const OpSemMemManager &getMainMemMgr() const { return m_main; }

  PtrSortTy ptrSort() const { return m_main.ptrSort(); }

  PtrTy salloc(unsigned int bytes, uint32_t align);

  PtrTy salloc(Expr elmts, unsigned int typeSz, uint32_t align);

  PtrTy mkStackPtr(unsigned int offset);

  PtrTy brk0Ptr() { return m_main.brk0Ptr(); }

  PtrTy halloc(unsigned int _bytes, uint32_t align);

  PtrTy halloc(Expr bytes, uint32_t align);

  PtrTy galloc(const GlobalVariable &gv, uint32_t align);

  PtrTy falloc(const Function &fn);
  PtrTy getPtrToFunction(const Function &F);

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv);

  void initGlobalVariable(const GlobalVariable &gv) const;

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const;

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const;

  PtrSortTy mkPtrRegisterSort(const Function &fn) const;

  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const;

  MemSortTy mkMemRegisterSort(const Instruction &inst) const;

  PtrTy freshPtr();

  PtrTy nullPtr() const;

  // We expect to get ONLY the following sorts:
  // 1. MemSortTy which is a struct with two members
  // 2. PtrSortTy  or Expr which is not a struct
  Expr coerce(Expr sort, Expr val);

  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const;

  PtrTy ptrAdd(PtrTy ptr, Expr offset) const;

  RawMemValTy memsetMetaData(const PtrTy ptr, unsigned int len, MemValTy memIn,
                             uint32_t align, unsigned int val);

  RawMemValTy memsetMetaData(const PtrTy ptr, Expr len, MemValTy memIn,
                             uint32_t align, unsigned int val);

  // This function reports a warning if there is a possibily for the
  // passed value to not be equal to 1.
  // This implies we tried to load memory that was never stored into.
  void CheckDefBeforeUse(Expr val);

  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                      uint64_t align);

  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                       uint64_t align);

  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align);

  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align);

  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const Type &ty,
                        uint64_t align);

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn, const Type &ty,
                           uint32_t align);

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned int len, MemValTy mem,
                  uint32_t align);

  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem, uint32_t align);

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned int len,
                  MemValTy memTrsfrRead, MemValTy memRead, uint32_t align);

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align);

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned int len, MemValTy mem,
                   uint32_t align);

  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const;

  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const;

  Expr ptrEq(PtrTy p1, PtrTy p2) const;

  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const;
  void onFunctionEntry(const Function &fn);
  void onModuleEntry(const Module &M) { m_main.onModuleEntry(M); }

  void dumpGlobalsMap();

  std::pair<char *, unsigned int>
  getGlobalVariableInitValue(const GlobalVariable &gv);

  MemValTy zeroedMemory() const;

  Expr isDereferenceable(PtrTy p, Expr byteSz);

  PtrTy getAddressable(PtrTy p) const;
};

} // namespace details
} // namespace seahorn
