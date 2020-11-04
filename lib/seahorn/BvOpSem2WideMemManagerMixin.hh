#pragma once

#include "BvOpSem2Context.hh"
#include "BvOpSem2TrackingRawMemMgr.hh"

#include <type_traits>

namespace seahorn {

namespace details {

template <typename BaseT>
class OpSemWideMemManagerMixin : public BaseT, public OpSemMemManager {

public:
  using Base = BaseT;
  using PtrTy = Expr;
  using MemRegTy = Expr;
  using MemValTy = Expr;
  using PtrSortTy = Expr;
  using MemSortTy = Expr;

  using BasePtrSortTy = typename Base::PtrSortTy;
  using BaseMemSortTy = typename Base::MemSortTy;

  using BasePtrTy = typename Base::PtrTy;
  using BaseMemRegTy = typename Base::MemRegTy;
  using BaseMemValTy = typename Base::MemValTy;

protected:
  Base &base() { return static_cast<Base &>(*this); }
  Base const &base() const { return static_cast<Base const &>(*this); }
  auto toPtrTy(BasePtrTy &&p) const { return static_cast<PtrTy>(p); }
  auto toMemValTy(BaseMemValTy &&m) const { return static_cast<MemValTy>(m); }
  auto toPtrSortTy(BasePtrSortTy &&s) const {
    return static_cast<PtrSortTy>(s);
  }
  auto toMemSortTy(BaseMemSortTy &&s) const {
    return static_cast<MemSortTy>(s);
  }

public:
  template <typename... Ts>
  OpSemWideMemManagerMixin(Ts &&... Args)
      : BaseT(std::forward<Ts>(Args)...),
        OpSemMemManager(base().sem(), base().ctx(), base().ptrSzInBytes(),
                        base().wordSzInBytes(), base().isIgnoreAlignment()) {}
  virtual ~OpSemWideMemManagerMixin() = default;

  PtrSortTy ptrSort() const override;

  PtrTy salloc(unsigned bytes, uint32_t align = 0) override;

  PtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0) override;

  PtrTy mkStackPtr(unsigned offset) override;

  PtrTy brk0Ptr() override;

  PtrTy halloc(unsigned _bytes, uint32_t align = 0) override;

  PtrTy halloc(Expr bytes, uint32_t align = 0) override;

  PtrTy galloc(const GlobalVariable &gv, uint32_t align = 0) override;

  PtrTy falloc(const Function &fn) override;

  PtrTy getPtrToFunction(const Function &F) override;

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv) override;

  void initGlobalVariable(const GlobalVariable &gv) const override;

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const override;

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const override;

  PtrSortTy mkPtrRegisterSort(const Function &fn) const override;

  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const override;

  MemSortTy mkMemRegisterSort(const Instruction &inst) const override;

  PtrTy freshPtr() override;

  PtrTy nullPtr() const override;

  // XXX figure out proper typing
  Expr coerce(Expr sort, Expr val) override;

  /// \brief Pointer addition with symbolic offset
  PtrTy ptrAdd(PtrTy ptr, Expr offset) const override;

  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const override;

  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                      uint64_t align) override;

  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                       uint64_t align) override;

  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align) override;

  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align) override;

  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const llvm::Type &ty,
                        uint64_t align) override;

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn,
                           const llvm::Type &ty, uint32_t align) override;

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                  uint32_t align) override;

  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                  uint32_t align) override;

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align) override;

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align) override;

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                   uint32_t align = 0) override;

  PtrTy inttoptr(Expr intVal, const Type &intTy,
                 const Type &ptrTy) const override;

  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const override;

  Expr ptrUlt(PtrTy p1, PtrTy p2) const override;

  Expr ptrSlt(PtrTy p1, PtrTy p2) const override;

  Expr ptrUle(PtrTy p1, PtrTy p2) const override;

  Expr ptrSle(PtrTy p1, PtrTy p2) const override;

  Expr ptrUgt(PtrTy p1, PtrTy p2) const override;

  Expr ptrSgt(PtrTy p1, PtrTy p2) const override;

  Expr ptrUge(PtrTy p1, PtrTy p2) const override;

  Expr ptrSge(PtrTy p1, PtrTy p2) const override;

  Expr ptrEq(PtrTy p1, PtrTy p2) const override;

  Expr ptrNe(PtrTy p1, PtrTy p2) const override;

  Expr ptrSub(PtrTy p1, PtrTy p2) const override;

  PtrTy gep(PtrTy ptr, gep_type_iterator it,
            gep_type_iterator end) const override;

  void onFunctionEntry(const Function &fn) override;

  void onModuleEntry(const Module &M) override;

  void dumpGlobalsMap() override;

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) override;

  MemValTy zeroedMemory() const override;

  Expr getFatData(PtrTy p, unsigned SlotIdx) override;

  /// \brief returns Expr after setting data.
  PtrTy setFatData(PtrTy p, unsigned SlotIdx, Expr data) override;

  Expr isDereferenceable(PtrTy p, Expr byteSz) override;

  MemValTy memsetMetaData(PtrTy ptr, unsigned int len, MemValTy memIn,
                          uint32_t align, unsigned int val) override;

  MemValTy memsetMetaData(PtrTy ptr, Expr len, MemValTy memIn, uint32_t align,
                          unsigned int val) override;

  Expr getMetaData(PtrTy ptr, PtrTy memIn, unsigned int byteSz,
                   uint32_t align) override;
  unsigned int getMetaDataMemWordSzInBits() override;
};

// 'HasTracking' is a solution for conditionally compiling in memory tracking
// code only when needed. It utilizes C++ metaprogramming and LLVM optimization.
// FIXME: It suffers from the shortcoming that unneeded calls cannot be
// completely removed by C++ metaprogramming which leads functions declared in
// OpSemMemManager being defined in *all* mem managers. Once we move to a SFINAE
// solution we will only need to define functions when they are
// used - faster to iterate through changes.
template <typename T> struct HasTracking : std::false_type {};

template <>
struct HasTracking<OpSemWideMemManagerMixin<TrackingRawMemManager>>
    : std::true_type {};

} // namespace details
} // namespace seahorn
