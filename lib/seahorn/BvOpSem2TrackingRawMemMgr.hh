#pragma once

#include "BvOpSem2Context.hh"
#include "BvOpSem2MemManagerMixin.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "seahorn/Expr/ExprOpStruct.hh"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"

#include "llvm/Support/MathExtras.h"
#include <array>
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
class TrackingRawMemManager : public MemManagerCore {
private:
  RawMemManager m_main;
  RawMemManager m_w_metadata;
  RawMemManager m_r_metadata;
  RawMemManager m_a_metadata;

  // All accesses to metadata memory managers should be through this map
  std::map<MetadataKind, RawMemManager *> m_metadata_map;

public:
  // This memory manager supports tracking
  using TrackingTag = MemoryFeatures::Tracking_tag;
  using FatMemTag = int;
  using WideMemTag = int;

  static const unsigned int g_MetadataBitWidth;
  static const unsigned int g_MetadataByteWidth;
  static const unsigned int g_num_slots;

  using PtrTy = OpSemMemManager::PtrTy;
  using PtrSortTy = OpSemMemManager::PtrSortTy;
  using MemRegTy = OpSemMemManager::MemRegTy;
  using RawMemValTy = OpSemMemManager::MemValTy;
  using RawMemSortTy = OpSemMemManager::MemSortTy;

  struct MemValTyImpl {
    // The order of metadata in a struct expr is expected to be the same as
    // the order in the enum MetadataKind
    Expr m_v;

    MemValTyImpl(RawMemValTy &&raw_val, RawMemValTy &&r_metadata_val,
                 RawMemValTy &&w_metadata_val, RawMemValTy &&a_metadata_val) {
      assert(!strct::isStructVal(raw_val));
      assert(!strct::isStructVal(r_metadata_val));
      assert(!strct::isStructVal(w_metadata_val));
      assert(!strct::isStructVal(a_metadata_val));
      std::array<RawMemValTy, 4> kids = {
          std::move(raw_val), std::move(r_metadata_val),
          std::move(w_metadata_val), std::move(a_metadata_val)};
      m_v = strct::mk(kids);
    }

    MemValTyImpl(const RawMemValTy &raw_val, const RawMemValTy &r_metadata_val,
                 const RawMemValTy &w_metadata_val,
                 const RawMemValTy &a_metadata_val) {
      assert(!strct::isStructVal(raw_val));
      assert(!strct::isStructVal(r_metadata_val));
      assert(!strct::isStructVal(w_metadata_val));
      assert(!strct::isStructVal(a_metadata_val));
      std::array<RawMemValTy, 4> kids = {raw_val, r_metadata_val,
                                         w_metadata_val, a_metadata_val};
      m_v = strct::mk(kids);
    }

    // Create a new MemValTyImpl object by copying from an existing object
    // except the metadata field given by 'kind'. Use raw_val for this field.
    MemValTyImpl(MetadataKind kind, const MemValTyImpl &orig_val,
                 const RawMemValTy &raw_val) {
      llvm::SmallVector<RawMemValTy, 4> kids;
      // Copy all fields from the original object one by one.
      for (unsigned i = 0, sz = orig_val.toExpr()->arity(); i < sz; ++i) {
        // kind + 1 indexes the intended kind in a compound expression.
        kids.push_back(i == (static_cast<std::size_t>(kind) + 1)
                           ? raw_val
                           : orig_val.toExpr()->arg(i));
      }
      m_v = strct::mk(kids);
    }

    explicit MemValTyImpl(const Expr &e) {
      // Our base is a struct of four exprs
      assert(!e || strct::isStructVal(e));
      assert(strct::isStructVal(e) && !strct::isStructVal(e->arg(0)));
      assert(strct::isStructVal(e) && !strct::isStructVal(e->arg(1)));
      assert(strct::isStructVal(e) && !strct::isStructVal(e->arg(2)));
      assert(strct::isStructVal(e) && !strct::isStructVal(e->arg(3)));
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawMemValTy getRaw() { return strct::extractVal(m_v, 0); }

    Expr getMetadata(MetadataKind kind) {
      return strct::extractVal(m_v, static_cast<std::size_t>(kind) + 1);
    }
  };

  struct MemSortTyImpl {
    Expr m_mem_sort;

    MemSortTyImpl(RawMemSortTy &&mem_sort, RawMemSortTy &&r_metadata_sort,
                  RawMemSortTy &&w_metadata_sort,
                  RawMemSortTy &&a_metadata_sort) {
      std::array<RawMemSortTy, 4> kids = {
          std::move(mem_sort), std::move(r_metadata_sort),
          std::move(w_metadata_sort), std::move(a_metadata_sort)};

      m_mem_sort = sort::structTy(kids);
    }

    MemSortTyImpl(const RawMemSortTy &mem_sort,
                  const RawMemSortTy &r_metadata_sort,
                  const RawMemSortTy &w_metadata_sort,
                  const RawMemSortTy &a_metadata_sort) {
      std::array<RawMemSortTy, 4> kids = {mem_sort, r_metadata_sort,
                                          w_metadata_sort, a_metadata_sort};

      m_mem_sort = sort::structTy(kids);
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

  TrackingRawMemManager::MemValTy memsetMetaData(MetadataKind kind, PtrTy ptr,
                                                 unsigned int len,
                                                 MemValTy memIn,
                                                 unsigned int val);

  TrackingRawMemManager::MemValTy memsetMetaData(MetadataKind kind, PtrTy ptr,
                                                 Expr len, MemValTy memIn,
                                                 unsigned int val);

  Expr getMetaData(MetadataKind kind, PtrTy ptr, MemValTy memIn,
                   unsigned int byteSz);

  /// \brief get word size (in bits) of Metadata memory, associated with a
  /// Tracking memory manager.
  // TODO: This should be replaced by a general way to query memory properties
  // from a memory manager.
  // All metadata memory will have the same word size.
  unsigned int getMetaDataMemWordSzInBits();

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

  /// \brief memset metadata memory associated with a Tracking Memory
  /// manager and return resulting memory. The 'raw' portion of memory is
  /// untouched.
  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned int len, MemValTy mem,
                  uint32_t align);

  /// \brief memset metadata memory associated with a Tracking Memory
  /// manager and return resulting memory. The 'raw' portion of memory is
  /// untouched.
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

  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const;
  void onFunctionEntry(const Function &fn);
  void onModuleEntry(const Module &M) { m_main.onModuleEntry(M); }

  void dumpGlobalsMap();

  std::pair<char *, unsigned int>
  getGlobalVariableInitValue(const GlobalVariable &gv);

  MemValTy zeroedMemory() const;

  Expr isDereferenceable(PtrTy p, Expr byteSz);

  PtrTy getAddressable(PtrTy p) const;

  bool isPtrTyVal(Expr e) const;

  Expr isMetadataSet(MetadataKind kind, PtrTy p, MemValTy mem);

  bool isMemVal(Expr e) const;

  TrackingRawMemManager::MemValTy
  setMetadata(MetadataKind kind, TrackingRawMemManager::PtrTy p,
              TrackingRawMemManager::MemValTy mem, unsigned val);
};

} // namespace details
} // namespace seahorn
