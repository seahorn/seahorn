#pragma once
#include "BvOpSem2Context.hh"

namespace seahorn {

using namespace seahorn::details;

template <typename BaseT>
class OpSemMemManagerMixin : public BaseT, public OpSemMemManager {

public:
  using Base = BaseT;
  using PtrTy = Expr;
  using MemRegTy = Expr;
  using MemValTy = Expr;

  using PtrSortTy = typename Base::PtrSortTy;
  using MemSortTy = typename Base::MemSortTy;

  using BasePtrTy = typename Base::PtrTy;
  using BaseMemRegTy = typename Base::MemRegTy;
  using BaseMemValTy = typename Base::MemValTy;

  template <typename... Ts>
  OpSemMemManagerMixin(Ts &&... Args)
      : BaseT(std::forward<Ts>(Args)...),
        OpSemMemManager(Base::sem(), Base::ctx(), Base::ptrSzInBytes(),
                        Base::wordSzInBytes()) {}
  virtual ~OpSemMemManagerMixin() = default;

  // XXX importing ptrSort directly from base did not work for some reason
  // using Base::ptrSort;
  PtrSortTy ptrSort() const override { return Base::ptrSort(); }

  PtrTy salloc(unsigned bytes, uint32_t align = 0) override {
    auto res = Base::salloc(bytes, align);
    return static_cast<PtrTy>(res);
  }

  PtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0) override {
    auto res = Base::salloc(elmts, typeSz, align);
    return static_cast<PtrTy>(res);
  }

  PtrTy mkStackPtr(unsigned offset) override {
    auto res = Base::mkStackPtr(offset);
    return static_cast<PtrTy>(res);
  }

  PtrTy brk0Ptr() override {
    auto res = Base::brk0Ptr();
    return static_cast<PtrTy>(res);
  }

  PtrTy halloc(unsigned _bytes, uint32_t align = 0) override {
    auto res = Base::halloc(_bytes, align);
    return static_cast<PtrTy>(res);
  }

  PtrTy halloc(Expr bytes, uint32_t align = 0) override {
    auto res = Base::halloc(bytes, align);
    return static_cast<PtrTy>(res);
  }

  PtrTy galloc(const GlobalVariable &gv, uint32_t align = 0) override {
    auto res = Base::galloc(gv, align);
    return static_cast<PtrTy>(res);
  }

  PtrTy falloc(const Function &fn) override {
    auto res = Base::falloc(fn);
    return static_cast<PtrTy>(res);
  }

  PtrTy getPtrToFunction(const Function &F) override {
    auto res = Base::getPtrToFunction(F);
    return static_cast<PtrTy>(res);
  }

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv) override {
    auto res = Base::getPtrToGlobalVariable(gv);
    return static_cast<PtrTy>(res);
  }

  void initGlobalVariable(const GlobalVariable &gv) const {
    Base::initGlobalVariable(gv);
  }

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const override {
    auto res = Base::mkAlignedPtr(name, align);
    return static_cast<PtrTy>(res);
  }

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const override {
    return Base::mkPtrRegisterSort(inst);
  }

  PtrSortTy mkPtrRegisterSort(const Function &fn) const override {
    return Base::mkPtrRegisterSort(fn);
  }

  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const override {
    return Base::mkPtrRegisterSort(gv);
  }

  MemSortTy mkMemRegisterSort(const Instruction &inst) const override {
    return Base::mkMemRegisterSort(inst);
  }

  PtrTy freshPtr() override {
    auto res = Base::freshPtr();
    return static_cast<PtrTy>(res);
  }

  PtrTy nullPtr() const override {
    auto res = Base::nullPtr();
    return static_cast<PtrTy>(res);
  }

  // XXX figure out proper typing
  Expr coerce(Expr sort, Expr val) override { return Base::coerce(sort, val); }

  /// \brief Pointer addition with symbolic offset
  PtrTy ptrAdd(PtrTy ptr, Expr offset) const override {
    auto res = Base::ptrAdd(BasePtrTy(std::move(ptr)), offset);
    return static_cast<PtrTy>(res);
  }

  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const override {
    auto res = Base::ptrAdd(BasePtrTy(std::move(ptr)), _offset);
    return static_cast<PtrTy>(res);
  }

  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                      uint64_t align) override {
    auto res = Base::loadIntFromMem(
        BasePtrTy(std::move(ptr)), BaseMemValTy(std::move(mem)), byteSz, align);
    return res;
  }

  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                       uint64_t align) override {
    auto res = Base::loadIntFromMem(
        BasePtrTy(std::move(ptr)), BaseMemValTy(std::move(mem)), byteSz, align);
    return static_cast<PtrTy>(res);
  }

  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align) override {
    auto res = Base::storeIntToMem(_val, BasePtrTy(std::move(ptr)),
                                   BaseMemValTy(std::move(mem)), byteSz, align);
    return static_cast<MemValTy>(res);
  }

  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align) override {
    auto res = Base::storePtrToMem(BasePtrTy(val), BasePtrTy(std::move(ptr)),
                                   BaseMemValTy(std::move(mem)), byteSz, align);
    return static_cast<MemValTy>(res);
  }

  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const llvm::Type &ty,
                        uint64_t align) override {
    auto res = Base::loadValueFromMem(BasePtrTy(std::move(ptr)),
                                      BaseMemValTy(std::move(mem)), ty, align);
    return res;
  }

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn,
                           const llvm::Type &ty, uint32_t align) override {
    auto res = Base::storeValueToMem(_val, BasePtrTy(std::move(ptr)),
                                     BaseMemValTy(std::move(memIn)), ty, align);
    return static_cast<MemValTy>(res);
  }

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                  uint32_t align) override {
    auto res = Base::MemSet(BasePtrTy(std::move(ptr)), _val, len,
                            BaseMemValTy(std::move(mem)), align);
    return static_cast<MemValTy>(res);
  }

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, MemValTy memTrsfrRead,
                  uint32_t align) override {
    auto res =
        Base::MemCpy(BasePtrTy(std::move(dPtr)), BasePtrTy(std::move(sPtr)),
                     len, BaseMemValTy(std::move(memTrsfrRead)), align);
    return static_cast<MemValTy>(res);
  }

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                   uint32_t align = 0) override {
    auto res = Base::MemFill(BasePtrTy(std::move(dPtr)), sPtr, len,
                             BaseMemValTy(std::move(mem)), align);
    return static_cast<MemValTy>(res);
  }

  PtrTy inttoptr(Expr intVal, const Type &intTy,
                 const Type &ptrTy) const override {
    auto res = Base::inttoptr(intVal, intTy, ptrTy);
    return static_cast<PtrTy>(res);
  }

  Expr ptrtoint(PtrTy ptr, const Type &ptrTy,
                const Type &intTy) const override {
    auto res = Base::ptrtoint(BasePtrTy(std::move(ptr)), ptrTy, intTy);
    return res;
  }

  Expr ptrUlt(PtrTy p1, PtrTy p2) const override {
    return Base::ptrUlt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }

  Expr ptrSlt(PtrTy p1, PtrTy p2) const override {
    return Base::ptrSlt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrUle(PtrTy p1, PtrTy p2) const override {
    return Base::ptrUle(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSle(PtrTy p1, PtrTy p2) const override {
    return Base::ptrSle(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrUgt(PtrTy p1, PtrTy p2) const override {
    return Base::ptrUgt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSgt(PtrTy p1, PtrTy p2) const override {
    return Base::ptrSgt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrUge(PtrTy p1, PtrTy p2) const override {
    return Base::ptrUge(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSge(PtrTy p1, PtrTy p2) const override {
    return Base::ptrSge(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrEq(PtrTy p1, PtrTy p2) const override {
    return Base::ptrEq(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrNe(PtrTy p1, PtrTy p2) const override {
    return Base::ptrNe(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSub(PtrTy p1, PtrTy p2) const override {
    return Base::ptrSub(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }

  PtrTy gep(PtrTy ptr, gep_type_iterator it,
            gep_type_iterator end) const override {
    auto res = Base::gep(BasePtrTy(std::move(ptr)), it, end);
    return static_cast<PtrTy>(res);
  }

  void onFunctionEntry(const Function &fn) override {
    Base::onFunctionEntry(fn);
  }

  void onModuleEntry(const Module &M) override { Base::onModuleEntry(M); }

  void dumpGlobalsMap() override { Base::dumpGlobalsMap(); }

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) override {
    return Base::getGlobalVariableInitValue(gv);
  }

  MemValTy zeroedMemory() const override {
    auto res = Base::zeroedMemory();
    return static_cast<MemValTy>(res);
  }

  Expr getFatData(PtrTy p, unsigned SlotIdx) override {
    auto res = Base::getFatData(BasePtrTy(std::move(p)), SlotIdx);
    return res;
  }

  /// \brief returns Expr after setting data.
  PtrTy setFatData(PtrTy p, unsigned SlotIdx, Expr data) override {
    auto res = Base::setFatData(BasePtrTy(std::move(p)), SlotIdx, data);
    return static_cast<PtrTy>(res);
  }
};
} // namespace seahorn
