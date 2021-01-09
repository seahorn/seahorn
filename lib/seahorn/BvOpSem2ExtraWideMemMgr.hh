#pragma once

#include "BvOpSem2Context.hh"
#include "BvOpSem2MemManagerMixin.hh"
#include "BvOpSem2RawMemMgr.hh"
#include "BvOpSem2TrackingRawMemMgr.hh"

#include "seahorn/Expr/ExprOpStruct.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Support/Stats.hh"

#include <fstream>

namespace seahorn {
namespace details {

template <class T> class ExtraWideMemManager : public MemManagerCore {

  /// \brief Base name for non-deterministic pointer
  Expr m_freshPtrName;

  /// \brief Source of unique identifiers
  mutable unsigned m_id;

  const Expr m_uninit_size;

  /// \brief Memory manager for raw pointers
  T m_main;
  /// \brief Memory manager for pointer offset

  // NOTE: offset bitwidth is same as ptr bitwidth since we need to
  // do arithmetic operations between them often.
  RawMemManager m_offset;
  /// \brief Memory manager for size
  RawMemManager m_size;

public:
  using TrackingTag = typename T::TrackingTag;
  // We don't support composing ExtraWideMemManager using FatMemManager
  using FatMemTag = int;
  using WideMemTag = MemoryFeatures::WideMem_tag;

  using RawPtrTy = typename T::PtrTy;
  using RawMemValTy = typename T::MemValTy;
  using RawPtrSortTy = typename T::PtrSortTy;
  using RawMemSortTy = typename T::MemSortTy;

  using MemRegTy = OpSemMemManager::MemRegTy;

  // size = size in bits
  struct PtrTyImpl {
    Expr m_v;

    PtrTyImpl(RawPtrTy &&base, Expr &&offset, Expr &&size) {
      m_v = strct::mk(std::move(base), std::move(offset), std::move(size));
    }

    PtrTyImpl(const RawPtrTy &base, const Expr offset, const Expr &size) {
      m_v = strct::mk(base, offset, size);
    }

    explicit PtrTyImpl(const Expr &e) {
      // Our base is a struct of three exprs
      assert(strct::isStructVal(e));
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawPtrTy getBase() { return strct::extractVal(m_v, 0); }

    Expr getOffset() { return strct::extractVal(m_v, 1); }

    Expr getSize() { return strct::extractVal(m_v, 2); }
  };

  struct MemValTyImpl {
    Expr m_v;

    MemValTyImpl(RawMemValTy &&raw_val, Expr &&offset_val, Expr &&size_val) {
      assert(!strct::isStructVal(size_val));
      m_v = strct::mk(std::move(raw_val), std::move(offset_val),
                      std::move(size_val));
    }

    MemValTyImpl(const RawPtrTy &raw_val, const Expr &offset_val,
                 const Expr &size_val) {
      assert(!strct::isStructVal(size_val));
      m_v = strct::mk(raw_val, offset_val, size_val);
    }

    explicit MemValTyImpl(const Expr &e) {
      // Our base is a struct of three exprs
      assert(strct::isStructVal(e));
      assert(!strct::isStructVal(e->arg(1)));
      assert(!strct::isStructVal(e->arg(2)));
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawMemValTy getRaw() { return strct::extractVal(m_v, 0); }

    Expr getOffset() { return strct::extractVal(m_v, 1); }

    Expr getSize() { return strct::extractVal(m_v, 2); }
  };

  struct PtrSortTyImpl {
    Expr m_ptr_sort;

    PtrSortTyImpl(RawPtrSortTy &&ptr_sort, Expr &&offset_sort,
                  Expr &&size_sort) {
      m_ptr_sort = sort::structTy(std::move(ptr_sort), std::move(offset_sort),
                                  std::move(size_sort));
    }

    PtrSortTyImpl(const RawPtrSortTy &ptr_sort, const Expr &offset_sort,
                  const Expr &size_sort) {
      m_ptr_sort = sort::structTy(ptr_sort, offset_sort, size_sort);
    }

    Expr v() const { return m_ptr_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawPtrSortTy getBaseSort() { return m_ptr_sort->arg(0); }
  };

  struct MemSortTyImpl {
    Expr m_mem_sort;

    MemSortTyImpl(RawMemSortTy &&mem_sort, Expr &&offset_sort,
                  Expr &&size_sort) {
      m_mem_sort = sort::structTy(std::move(mem_sort), std::move(offset_sort),
                                  std::move(size_sort));
    }

    MemSortTyImpl(const RawMemSortTy &mem_sort, Expr &offset_sort,
                  const Expr &size_sort) {
      m_mem_sort = sort::structTy(mem_sort, offset_sort, size_sort);
    }

    Expr v() const { return m_mem_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }
  };

  using PtrTy = PtrTyImpl;
  using PtrSortTy = PtrSortTyImpl;
  using MemValTy = MemValTyImpl;
  using MemSortTy = MemSortTyImpl;

  /// \brief A null pointer expression (cache)
  PtrTy m_nullPtr;

  ExtraWideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                      unsigned wordSz, bool useLambdas = false);

  ~ExtraWideMemManager() = default;

  Expr bytesToSlotExpr(unsigned bytes);

  PtrSortTy ptrSort() const;

  PtrTy salloc(unsigned int bytes, uint32_t align);

  PtrTy salloc(Expr elmts, unsigned int typeSz, uint32_t align);

  PtrTy mkStackPtr(unsigned int offset);

  PtrTy brk0Ptr();

  PtrTy halloc(unsigned int _bytes, uint32_t align);

  PtrTy halloc(Expr bytes, uint32_t align);

  PtrTy galloc(const GlobalVariable &gv, uint32_t align);

  PtrTy falloc(const Function &fn);

  // TODO: What is the right size to return here?
  PtrTy getPtrToFunction(const Function &F);

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv);

  void initGlobalVariable(const GlobalVariable &gv) const;

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const;

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const;

  PtrSortTy mkPtrRegisterSort(const Function &fn) const;

  /// \brief Returns sort of a pointer register for a global pointer
  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const;

  MemSortTy mkMemRegisterSort(const Instruction &inst) const;

  PtrTy freshPtr();

  PtrTy nullPtr() const;

  // We expect to get ONLY the following sorts:
  // 1. MemSortTy, PtrSortTy - each is a struct with three members
  // 2. Expr which is not a struct
  Expr coerce(Expr sort, Expr val);

  PtrTy ptrAdd(PtrTy base, int32_t _offset) const;

  PtrTy ptrAdd(PtrTy base, Expr offset) const;

  Expr loadIntFromMem(PtrTy base, MemValTy mem, unsigned int byteSz,
                      uint64_t align);

  PtrTy loadPtrFromMem(PtrTy base, MemValTy mem, unsigned int byteSz,
                       uint64_t align);

  MemValTy storeIntToMem(Expr _val, PtrTy base, MemValTy mem,
                         unsigned int byteSz, uint64_t align);

  MemValTy storePtrToMem(PtrTy val, PtrTy base, MemValTy mem,
                         unsigned int byteSz, uint64_t align);

  Expr loadValueFromMem(PtrTy base, MemValTy mem, const Type &ty,
                        uint64_t align);

  MemValTy storeValueToMem(Expr _val, PtrTy base, MemValTy memIn,
                           const Type &ty, uint32_t align);

  MemValTy MemSet(PtrTy base, Expr _val, unsigned int len, MemValTy mem,
                  uint32_t align);

  MemValTy MemSet(PtrTy base, Expr _val, Expr len, MemValTy mem,
                  uint32_t align);

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned int len,
                  MemValTy memTrsfrRead, MemValTy memRead, uint32_t align);

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align);

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned int len, MemValTy mem,
                   uint32_t align);

  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const;

  Expr ptrtoint(PtrTy base, const Type &ptrTy, const Type &intTy) const;

  PtrTy gep(PtrTy base, gep_type_iterator it, gep_type_iterator end) const;

  void onFunctionEntry(const Function &fn);

  void onModuleEntry(const Module &M);

  void dumpGlobalsMap();

  std::pair<char *, unsigned int>
  getGlobalVariableInitValue(const GlobalVariable &gv);

  MemValTy zeroedMemory() const;

  Expr isDereferenceable(PtrTy p, Expr byteSz);

  typename ExtraWideMemManager<T>::RawMemValTy
  setModified(ExtraWideMemManager::PtrTy ptr,
              ExtraWideMemManager::MemValTy mem);

  Expr isMetadataSet(MetadataKind kind, ExtraWideMemManager::PtrTy ptr,
                     ExtraWideMemManager::MemValTy mem);

  typename ExtraWideMemManager<T>::MemValTy
  setMetadata(MetadataKind kind, ExtraWideMemManager::PtrTy ptr,
              ExtraWideMemManager::MemValTy mem, unsigned val);

  typename ExtraWideMemManager<T>::MemValTy
  memsetMetaData(MetadataKind kind, ExtraWideMemManager::PtrTy ptr,
                 unsigned int len, ExtraWideMemManager::MemValTy memIn,
                 unsigned int val);

  typename ExtraWideMemManager<T>::MemValTy
  memsetMetaData(MetadataKind kind, ExtraWideMemManager::PtrTy ptr, Expr len,
                 ExtraWideMemManager::MemValTy memIn, unsigned int val);

  Expr getMetaData(MetadataKind kind, PtrTy ptr, MemValTy memIn,
                   unsigned int byteSz);

  unsigned int getMetaDataMemWordSzInBits();

  RawPtrTy getAddressable(PtrTy p) const;

  bool isPtrTyVal(Expr e) const;

  bool isMemVal(Expr e) const;

  Expr getSize(PtrTy p) const;

  const OpSemMemManager &getMainMemMgr() const;

  Expr castPtrSzToSlotSz(const Expr val) const;

  Expr ptrEq(PtrTy p1, PtrTy p2) const;
  Expr ptrUlt(PtrTy p1, PtrTy p2) const;
  Expr ptrSlt(PtrTy p1, PtrTy p2) const;
  Expr ptrUle(PtrTy p1, PtrTy p2) const;
  Expr ptrSle(PtrTy p1, PtrTy p2) const;
  Expr ptrUgt(PtrTy p1, PtrTy p2) const;
  Expr ptrSgt(PtrTy p1, PtrTy p2) const;
  Expr ptrUge(PtrTy p1, PtrTy p2) const;
  Expr ptrSge(PtrTy p1, PtrTy p2) const;
  Expr ptrNe(PtrTy p1, PtrTy p2) const;
  Expr ptrSub(PtrTy p1, PtrTy p2) const;
};

OpSemMemManager *mkExtraWideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                       unsigned ptrSz, unsigned wordSz,
                                       bool useLambdas);

OpSemMemManager *mkTrackingExtraWideMemManager(Bv2OpSem &sem,
                                               Bv2OpSemContext &ctx,
                                               unsigned ptrSz, unsigned wordSz,
                                               bool useLambdas);
} // namespace details
} // namespace seahorn
