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

#include <boost/hana/ext/std/integral_constant.hpp>

#define MAIN_MEM_MGR hana::at_key(m_submgrs, BOOST_HANA_STRING("m_main"))

namespace seahorn {
namespace details {

/// \brief Container for sub memory managers to be passed to TrackingRawMemMgr
//
// Adding a new element (shadow slot) involves adding a new memory manager
// inside this and in MetadataKind Use of MetadataKind is still needed because
// setMetadata and getMetadata methods are virtual and thus calls to specific
// metadata sub managers cannot be resolved at compile-time.
struct TrackingMemoryTuple {
  BOOST_HANA_DEFINE_STRUCT(TrackingMemoryTuple, (RawMemManager, m_main),
                           (RawMemManager, m_r_metadata),
                           (RawMemManager, m_w_metadata),
                           (RawMemManager, m_a_metadata),
                           (RawMemManager, m_c0_metadata));

  /// \brief A helper function to get number of memory elements in tuple
  static constexpr auto GetTupleSize() {
    constexpr auto accessors = hana::accessors<TrackingMemoryTuple>();
    return hana::size(accessors);
  }

  TrackingMemoryTuple(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                      unsigned wordSz, bool useLambdas);

  TrackingMemoryTuple(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                      unsigned wordSz, bool useLambdas, bool ignoreAlignment);

  ~TrackingMemoryTuple() = default;
};

// This memory manager adds a metadata memory(backed by raw memory) sitting side
// by side to conventional memory(backed by raw memory). The word size for
// conventional memory can be greater than metadata memory.
//
// Currently this implementation has a metadata memory word size of 1 byte.
class TrackingRawMemManager : public MemManagerCore {
private:
  TrackingMemoryTuple m_submgrs;

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
    Expr m_v;

    // Dummy function to typecheck the args passed to MemValTyImpl ctor
    template <typename R, typename...> struct fst { typedef R type; };

    /// \Brief Construct only with a tuple of RawMemValTy elements
    //
    // The second template param can be interpreted as follows
    // 1. If each element of the passed tuple is_same as RawMemValTy, then
    // 2. set enable_if to true and consequently the second template parameter
    // in
    //    fst to void..., finally
    // 3. fst::type is the second template param
    template <typename... Args,
              typename = typename fst<
                  void, typename std::enable_if<std::is_same<
                            Args, RawMemValTy>::value>::type...>::type>
    explicit MemValTyImpl(hana::tuple<Args &&...> args) {
      BOOST_HANA_CONSTANT_ASSERT(hana::size(args) ==
                                 TrackingMemoryTuple::GetTupleSize());
      hana::for_each(
          args, [&](auto element) { assert(!strct::isStructVal(element)); });
      auto a = hana::unpack(args, [](auto... i) {
        return std::array<RawMemValTy, sizeof...(i)>{{std::move(i)...}};
      });
      m_v = strct::mk(a);
    }

    template <typename... Args,
              typename = typename fst<
                  void, typename std::enable_if<std::is_same<
                            Args, RawMemValTy>::value>::type...>::type>
    explicit MemValTyImpl(hana::tuple<Args...> args) {
      BOOST_HANA_CONSTANT_ASSERT(hana::size(args) ==
                                 TrackingMemoryTuple::GetTupleSize());
      hana::for_each(
          args, [&](auto element) { assert(!strct::isStructVal(element)); });
      auto a = hana::unpack(args, [](auto... i) {
        return std::array<RawMemValTy, sizeof...(i)>{{i...}};
      });
      m_v = strct::mk(a);
    }

    explicit MemValTyImpl(const Expr &e) {
      // Our base is a struct of primitive(non-struct) exprs
      assert(!e || strct::isStructVal(e));
      auto range =
          hana::range_c<size_t, 0, TrackingMemoryTuple::GetTupleSize()>;
      auto indices_tuple = hana::to_tuple(range);
      hana::for_each(indices_tuple, [&](auto element) {
        assert(!strct::isStructVal(e->arg(element)));
      });
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawMemValTy getRaw() { return strct::extractVal(m_v, 0); }

    Expr getElementVal(size_t index) { return strct::extractVal(m_v, index); }

    auto tail() {
      auto indices =
          hana::make_range(hana::int_c<1>, TrackingMemoryTuple::GetTupleSize());
      auto indices_t = hana::to_tuple(indices);
      auto exprs = hana::transform(
          indices_t, [this](size_t i) { return this->getElementVal(i); });
      return exprs;
    }
  };

  struct MemSortTyImpl {
    Expr m_sort_v;

    // Dummy function to typecheck the args passed to MemSortTyImpl ctor
    template <typename R, typename...> struct fst { typedef R type; };

    /// \Brief Construct only with a tuple of RawMemValTy elements
    //
    // See MemValTyImpl ctor for details.
    template <typename... Args,
              typename = typename fst<
                  void, typename std::enable_if<std::is_same<
                            Args, RawMemSortTy>::value>::type...>::type>
    explicit MemSortTyImpl(hana::tuple<Args &&...> args) {
      BOOST_HANA_CONSTANT_ASSERT(hana::size(args) ==
                                 TrackingMemoryTuple::GetTupleSize());
      auto a = hana::unpack(args, [](auto... i) {
        return std::array<RawMemSortTy, sizeof...(i)>{{std::move(i)...}};
      });
      m_sort_v = sort::structTy(a);
    }

    template <typename... Args,
              typename = typename fst<
                  void, typename std::enable_if<std::is_same<
                            Args, RawMemSortTy>::value>::type...>::type>
    explicit MemSortTyImpl(hana::tuple<Args...> args) {
      BOOST_HANA_CONSTANT_ASSERT(hana::size(args) ==
                                 TrackingMemoryTuple::GetTupleSize());
      auto a = hana::unpack(args, [](auto... i) {
        return std::array<RawMemSortTy, sizeof...(i)>{{i...}};
      });
      m_sort_v = sort::structTy(a);
    }

    Expr v() const { return m_sort_v; }
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

  OpSemAllocator &getMAllocator() const { return MAIN_MEM_MGR.getMAllocator(); }

  const OpSemMemManager &getMainMemMgr() const { return MAIN_MEM_MGR; }

  PtrSortTy ptrSort() const { return MAIN_MEM_MGR.ptrSort(); }

  PtrTy salloc(unsigned int bytes, uint32_t align);

  PtrTy salloc(Expr elmts, unsigned int typeSz, uint32_t align);

  PtrTy mkStackPtr(unsigned int offset);

  PtrTy brk0Ptr() { return MAIN_MEM_MGR.brk0Ptr(); }

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

  TrackingRawMemManager::MemValTy memsetMetadata(MetadataKind kind, PtrTy ptr,
                                                 unsigned int len,
                                                 MemValTy memIn,
                                                 unsigned int val);

  TrackingRawMemManager::MemValTy memsetMetadata(MetadataKind kind, PtrTy ptr,
                                                 Expr len, MemValTy memIn,
                                                 unsigned int val);

  Expr getMetadata(MetadataKind kind, PtrTy ptr, MemValTy memIn,
                   unsigned int byteSz);

  /// \brief get word size (in bits) of Metadata memory, associated with a
  /// Tracking memory manager.
  // TODO: This should be replaced by a general way to query memory properties
  // from a memory manager.
  // All metadata memory will have the same word size.
  unsigned int getMetadataMemWordSzInBits();

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
  void onModuleEntry(const Module &M) { MAIN_MEM_MGR.onModuleEntry(M); }

  void dumpGlobalsMap();

  std::pair<char *, unsigned int>
  getGlobalVariableInitValue(const GlobalVariable &gv);

  MemValTy zeroedMemory() const;

  Expr isDereferenceable(PtrTy p, Expr byteSz);

  PtrTy getAddressable(PtrTy p) const;

  bool isPtrTyVal(Expr e) const;

  Expr isMetadataSet(MetadataKind kind, PtrTy p, MemValTy mem);

  bool isMemVal(Expr e) const;

  MemValTy setMetadata(MetadataKind kind, TrackingRawMemManager::PtrTy p,
                       TrackingRawMemManager::MemValTy mem, Expr val);
  size_t getNumOfMetadataSlots();
};

} // namespace details
} // namespace seahorn
