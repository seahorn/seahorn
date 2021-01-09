#pragma once
#include "BvOpSem2Context.hh"

namespace seahorn {
namespace details {
template <typename BaseT>
class OpSemMemManagerMixin : public BaseT, public OpSemMemManager {

public:
  using TrackingTag = typename BaseT::TrackingTag;
  using FatMemTag = typename BaseT::FatMemTag;
  using WideMemTag = typename BaseT::WideMemTag;

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
  OpSemMemManagerMixin(Ts &&... Args)
      : BaseT(std::forward<Ts>(Args)...),
        OpSemMemManager(base().sem(), base().ctx(), base().ptrSizeInBytes(),
                        base().wordSizeInBytes(), base().isIgnoreAlignment()) {}
  virtual ~OpSemMemManagerMixin() = default;

  PtrSortTy ptrSort() const override {
    auto res = base().ptrSort();
    return toPtrSortTy(std::move(res));
  }

  PtrTy salloc(unsigned bytes, uint32_t align = 0) override {
    auto res = base().salloc(bytes, align);
    return toPtrTy(std::move(res));
  }

  PtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0) override {
    auto res = base().salloc(elmts, typeSz, align);
    return toPtrTy(std::move(res));
  }

  PtrTy mkStackPtr(unsigned offset) override {
    auto res = base().mkStackPtr(offset);
    return toPtrTy(std::move(res));
  }

  PtrTy brk0Ptr() override {
    auto res = base().brk0Ptr();
    return toPtrTy(std::move(res));
  }

  PtrTy halloc(unsigned _bytes, uint32_t align = 0) override {
    auto res = base().halloc(_bytes, align);
    return toPtrTy(std::move(res));
  }

  PtrTy halloc(Expr bytes, uint32_t align = 0) override {
    auto res = base().halloc(bytes, align);
    return toPtrTy(std::move(res));
  }

  PtrTy galloc(const GlobalVariable &gv, uint32_t align = 0) override {
    auto res = base().galloc(gv, align);
    return toPtrTy(std::move(res));
  }

  PtrTy falloc(const Function &fn) override {
    auto res = base().falloc(fn);
    return toPtrTy(std::move(res));
  }

  PtrTy getPtrToFunction(const Function &F) override {
    auto res = base().getPtrToFunction(F);
    return toPtrTy(std::move(res));
  }

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv) override {
    auto res = base().getPtrToGlobalVariable(gv);
    return toPtrTy(std::move(res));
  }

  void initGlobalVariable(const GlobalVariable &gv) const {
    base().initGlobalVariable(gv);
  }

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const override {
    auto res = base().mkAlignedPtr(name, align);
    return toPtrTy(std::move(res));
  }

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const override {
    auto res = base().mkPtrRegisterSort(inst);
    return toPtrSortTy(std::move(res));
  }

  PtrSortTy mkPtrRegisterSort(const Function &fn) const override {
    auto res = base().mkPtrRegisterSort(fn);
    return toPtrSortTy(std::move(res));
  }

  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const override {
    auto res = base().mkPtrRegisterSort(gv);
    return toPtrSortTy(std::move(res));
  }

  MemSortTy mkMemRegisterSort(const Instruction &inst) const override {
    auto res = base().mkMemRegisterSort(inst);
    return toMemSortTy(std::move(res));
  }

  PtrTy freshPtr() override {
    auto res = base().freshPtr();
    return toPtrTy(std::move(res));
  }

  PtrTy nullPtr() const override {
    auto res = base().nullPtr();
    return toPtrTy(std::move(res));
  }

  // XXX figure out proper typing
  Expr coerce(Expr sort, Expr val) override { return base().coerce(sort, val); }

  /// \brief Pointer addition with symbolic offset
  PtrTy ptrAdd(PtrTy ptr, Expr offset) const override {
    auto res = base().ptrAdd(BasePtrTy(std::move(ptr)), offset);
    return toPtrTy(std::move(res));
  }

  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const override {
    auto res = base().ptrAdd(BasePtrTy(std::move(ptr)), _offset);
    return toPtrTy(std::move(res));
  }

  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                      uint64_t align) override {
    auto res = base().loadIntFromMem(
        BasePtrTy(std::move(ptr)), BaseMemValTy(std::move(mem)), byteSz, align);
    return res;
  }

  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                       uint64_t align) override {
    auto res = base().loadPtrFromMem(
        BasePtrTy(std::move(ptr)), BaseMemValTy(std::move(mem)), byteSz, align);
    return toPtrTy(std::move(res));
  }

  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align) override {
    auto res =
        base().storeIntToMem(_val, BasePtrTy(std::move(ptr)),
                             BaseMemValTy(std::move(mem)), byteSz, align);
    return toMemValTy(std::move(res));
  }

  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align) override {
    auto res =
        base().storePtrToMem(BasePtrTy(val), BasePtrTy(std::move(ptr)),
                             BaseMemValTy(std::move(mem)), byteSz, align);
    return toMemValTy(std::move(res));
  }

  // TODO: move common logic from memmgr to mixin.
  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const llvm::Type &ty,
                        uint64_t align) override {
    auto res = base().loadValueFromMem(BasePtrTy(std::move(ptr)),
                                       BaseMemValTy(std::move(mem)), ty, align);
    return res;
  }

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn,
                           const llvm::Type &ty, uint32_t align) override {
    auto res =
        base().storeValueToMem(_val, BasePtrTy(std::move(ptr)),
                               BaseMemValTy(std::move(memIn)), ty, align);
    return toMemValTy(std::move(res));
  }

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                  uint32_t align) override {
    auto res = base().MemSet(BasePtrTy(std::move(ptr)), _val, len,
                             BaseMemValTy(std::move(mem)), align);
    return toMemValTy(std::move(res));
  }

  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                  uint32_t align) override {
    auto res = base().MemSet(BasePtrTy(std::move(ptr)), _val, len,
                             BaseMemValTy(std::move(mem)), align);
    return toMemValTy(std::move(res));
  }

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align) override {
    auto res =
        base().MemCpy(BasePtrTy(std::move(dPtr)), BasePtrTy(std::move(sPtr)),
                      len, BaseMemValTy(std::move(memTrsfrRead)),
                      BaseMemValTy(std::move(memRead)), align);
    return toMemValTy(std::move(res));
  }

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align) override {
    auto res =
        base().MemCpy(BasePtrTy(std::move(dPtr)), BasePtrTy(std::move(sPtr)),
                      len, BaseMemValTy(std::move(memTrsfrRead)),
                      BaseMemValTy(std::move(memRead)), align);
    return toMemValTy(std::move(res));
  }

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                   uint32_t align = 0) override {
    auto res = base().MemFill(BasePtrTy(std::move(dPtr)), sPtr, len,
                              BaseMemValTy(std::move(mem)), align);
    return toMemValTy(std::move(res));
  }

  PtrTy inttoptr(Expr intVal, const Type &intTy,
                 const Type &ptrTy) const override {
    auto res = base().inttoptr(intVal, intTy, ptrTy);
    return toPtrTy(std::move(res));
  }

  Expr ptrtoint(PtrTy ptr, const Type &ptrTy,
                const Type &intTy) const override {
    auto res = base().ptrtoint(BasePtrTy(std::move(ptr)), ptrTy, intTy);
    return res;
  }

  Expr ptrUlt(PtrTy p1, PtrTy p2) const override {
    return base().ptrUlt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }

  Expr ptrSlt(PtrTy p1, PtrTy p2) const override {
    return base().ptrSlt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrUle(PtrTy p1, PtrTy p2) const override {
    return base().ptrUle(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSle(PtrTy p1, PtrTy p2) const override {
    return base().ptrSle(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrUgt(PtrTy p1, PtrTy p2) const override {
    return base().ptrUgt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSgt(PtrTy p1, PtrTy p2) const override {
    return base().ptrSgt(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrUge(PtrTy p1, PtrTy p2) const override {
    return base().ptrUge(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSge(PtrTy p1, PtrTy p2) const override {
    return base().ptrSge(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrEq(PtrTy p1, PtrTy p2) const override {
    return base().ptrEq(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrNe(PtrTy p1, PtrTy p2) const override {
    return base().ptrNe(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }
  Expr ptrSub(PtrTy p1, PtrTy p2) const override {
    return base().ptrSub(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
  }

  PtrTy gep(PtrTy ptr, gep_type_iterator it,
            gep_type_iterator end) const override {
    auto res = base().gep(BasePtrTy(std::move(ptr)), it, end);
    return toPtrTy(std::move(res));
  }

  void onFunctionEntry(const Function &fn) override {
    base().onFunctionEntry(fn);
  }

  void onModuleEntry(const Module &M) override { base().onModuleEntry(M); }

  void dumpGlobalsMap() override { base().dumpGlobalsMap(); }

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) override {
    return base().getGlobalVariableInitValue(gv);
  }

  MemValTy zeroedMemory() const override {
    auto res = base().zeroedMemory();
    return toMemValTy(std::move(res));
  }

  Expr getFatData(PtrTy p, unsigned SlotIdx) override {
    return hana::eval_if(
        MemoryFeatures::has_fatmem(hana::type<BaseT>{}),
        [&](auto _) {
          auto res = _(base()).getFatData(BasePtrTy(std::move(p)), SlotIdx);
          return res;
        },
        [&] {
          LOG("opsem", WARN << "getFatData() not implemented!\n");
          return Expr();
        });
  }

  /// \brief returns Expr after setting data.
  PtrTy setFatData(PtrTy p, unsigned SlotIdx, Expr data) override {
    return hana::eval_if(
        MemoryFeatures::has_fatmem(hana::type<BaseT>{}),
        [&](auto _) {
          auto res =
              _(base()).setFatData(BasePtrTy(std::move(p)), SlotIdx, data);
          return toPtrTy(std::move(res));
        },
        [&] {
          LOG("opsem", WARN << "setFatData() not implemented!\n");
          return p;
        });
  }

  Expr isDereferenceable(PtrTy p, Expr byteSz) override {
    return hana::eval_if(
        MemoryFeatures::has_widemem(hana::type<BaseT>{}),
        [&](auto _) {
          return _(base()).isDereferenceable(BasePtrTy(std::move(p)), byteSz);
        },
        [&] {
          LOG("opsem", WARN << "isDerefernceable() not implemented!\n");
          return Expr();
        });
  }

  MemValTy setMetadata(MetadataKind kind, PtrTy p, MemValTy mem,
                       unsigned val) override {
    return hana::eval_if(
        MemoryFeatures::has_tracking(hana::type<BaseT>{}),
        [&](auto _) {
          return toMemValTy(std::move(
              _(base()).setMetadata(kind, BasePtrTy(std::move(p)),
                                    BaseMemValTy(std::move(mem)), val)));
        },
        [&] {
          LOG("opsem.memtrack.verbose",
              WARN << "setMetadata() not implemented!\n");
          return mem;
        });
  }

  unsigned int getMetaDataMemWordSzInBits() {
    return hana::eval_if(
        MemoryFeatures::has_tracking(hana::type<BaseT>{}),
        [&](auto _) { return _(base()).getMetaDataMemWordSzInBits(); },
        [&] { return 0; });
  }

  Expr isMetadataSet(MetadataKind kind, PtrTy p, MemValTy mem) override {
    return hana::eval_if(
        MemoryFeatures::has_tracking(hana::type<BaseT>{}),
        [&](auto _) {
          return _(base()).isMetadataSet(kind, BasePtrTy(std::move(p)),
                                         BaseMemValTy(std::move(mem)));
        },
        [&] {
          LOG("opsem.memtrack.verbose",
              WARN << "isMetadataSet() not implemented!\n");
          return Expr();
        });
  }

  Expr getMetaData(MetadataKind kind, PtrTy p, MemValTy memIn,
                   unsigned int byteSz) {
    return hana::eval_if(
        MemoryFeatures::has_tracking(hana::type<BaseT>{}),
        [&](auto _) {
          return _(base()).getMetaData(kind, BasePtrTy(std::move(p)),
                                       BaseMemValTy(std::move(memIn)), byteSz);
        },
        [&] { return Expr(); });
  }

  MemValTy memsetMetaData(MetadataKind kind, PtrTy p, Expr len, MemValTy memIn,
                          unsigned int val) {
    return hana::eval_if(
        MemoryFeatures::has_tracking(hana::type<BaseT>{}),
        [&](auto _) {
          auto r =
              _(base()).memsetMetaData(kind, BasePtrTy(std::move(p)), len,
                                       BaseMemValTy(std::move(memIn)), val);
          return toMemValTy(std::move(r));
        },
        [&] { return memIn; });
  }

  MemValTy memsetMetaData(MetadataKind kind, PtrTy p, unsigned int len,
                          MemValTy memIn, unsigned int val) {
    return hana::eval_if(
        MemoryFeatures::has_tracking(hana::type<BaseT>{}),
        [&](auto _) {
          auto r =
              _(base()).memsetMetaData(kind, BasePtrTy(std::move(p)), len,
                                       BaseMemValTy(std::move(memIn)), val);
          return toMemValTy(std::move(r));
        },
        [&] { return memIn; });
  }

  bool isPtrTyVal(Expr e) { return base().isPtrTyVal(e); }

  Expr ptrToAddr(Expr p) {
    if (!isPtrTyVal(p))
      return Expr();
    return Expr(base().getAddressable(BasePtrTy(p)));
  }

  bool isMemVal(Expr e) { return base().isMemVal(e); }

  Expr getRawMem(Expr e) {
    if (!isMemVal(e))
      return Expr();
    return Expr(BaseMemValTy(e).getRaw());
  }
};
} // namespace details
} // namespace seahorn
