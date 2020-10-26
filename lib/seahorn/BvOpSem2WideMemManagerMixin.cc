#include "BvOpSem2WideMemManagerMixin.hh"
#include "BvOpSem2ExtraWideMemMgr.hh"
#include "BvOpSem2TrackingRawMemMgr.hh"
#include "BvOpSem2WideMemMgr.hh"

namespace seahorn {

namespace details {
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::zeroedMemory() const {
  auto res = base().zeroedMemory();
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::setFatData(OpSemWideMemManagerMixin::PtrTy p,
                                            unsigned int SlotIdx, Expr data) {
  LOG("opsem", WARN << "setFatData() not implemented!\n");
  return toPtrTy(std::move(base().nullPtr()));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::isDereferenceable(
    OpSemWideMemManagerMixin::PtrTy p, Expr byteSz) {
  return base().isDereferenceable(BasePtrTy(std::move(p)), byteSz);
}
template <typename BaseT>
std::pair<char *, unsigned>
OpSemWideMemManagerMixin<BaseT>::getGlobalVariableInitValue(
    const GlobalVariable &gv) {
  return base().getGlobalVariableInitValue(gv);
}
template <typename BaseT>
void OpSemWideMemManagerMixin<BaseT>::dumpGlobalsMap() {
  base().dumpGlobalsMap();
}
template <typename BaseT>
void OpSemWideMemManagerMixin<BaseT>::onModuleEntry(const Module &M) {
  base().onModuleEntry(M);
}
template <typename BaseT>
void OpSemWideMemManagerMixin<BaseT>::onFunctionEntry(const Function &fn) {
  base().onFunctionEntry(fn);
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::gep(OpSemWideMemManagerMixin::PtrTy ptr,
                                     gep_type_iterator it,
                                     gep_type_iterator end) const {
  auto res = base().gep(BasePtrTy(std::move(ptr)), it, end);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrSub(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrSub(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrNe(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrNe(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrEq(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().ptrEq(BasePtrTy(std::move(p1)), BasePtrTy(std::move(p2)));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrUge(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrUge(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrSge(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrSge(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrSgt(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrSgt(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrUgt(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrUgt(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrSle(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrSle(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrUle(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrUle(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrSlt(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrSlt(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrUlt(
    OpSemWideMemManagerMixin::PtrTy p1,
    OpSemWideMemManagerMixin::PtrTy p2) const {
  return base().getMainMemMgr().ptrUlt(
      base().getAddressable(BasePtrTy(std::move(p1))),
      base().getAddressable(BasePtrTy(std::move(p2))));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::ptrtoint(
    OpSemWideMemManagerMixin::PtrTy ptr, const Type &ptrTy,
    const Type &intTy) const {
  auto res = base().ptrtoint(BasePtrTy(std::move(ptr)), ptrTy, intTy);
  return res;
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::inttoptr(Expr intVal, const Type &intTy,
                                          const Type &ptrTy) const {
  auto res = base().inttoptr(intVal, intTy, ptrTy);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::MemFill(
    typename OpSemWideMemManagerMixin<BaseT>::PtrTy dPtr, char *sPtr,
    unsigned int len, OpSemWideMemManagerMixin::MemValTy mem, uint32_t align) {
  auto res = base().MemFill(BasePtrTy(std::move(dPtr)), sPtr, len,
                            BaseMemValTy(std::move(mem)), align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::MemCpy(
    OpSemWideMemManagerMixin::PtrTy dPtr, OpSemWideMemManagerMixin::PtrTy sPtr,
    Expr len, OpSemWideMemManagerMixin::MemValTy memTrsfrRead,
    OpSemWideMemManagerMixin::MemValTy memRead, uint32_t align) {
  auto res =
      base().MemCpy(BasePtrTy(std::move(dPtr)), BasePtrTy(std::move(sPtr)), len,
                    BaseMemValTy(std::move(memTrsfrRead)),
                    BaseMemValTy(std::move(memRead)), align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::MemCpy(
    OpSemWideMemManagerMixin::PtrTy dPtr, OpSemWideMemManagerMixin::PtrTy sPtr,
    unsigned int len, OpSemWideMemManagerMixin::MemValTy memTrsfrRead,
    OpSemWideMemManagerMixin::MemValTy memRead, uint32_t align) {
  auto res =
      base().MemCpy(BasePtrTy(std::move(dPtr)), BasePtrTy(std::move(sPtr)), len,
                    BaseMemValTy(std::move(memTrsfrRead)),
                    BaseMemValTy(std::move(memRead)), align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::MemSet(OpSemWideMemManagerMixin::PtrTy ptr,
                                        Expr _val, Expr len,
                                        OpSemWideMemManagerMixin::MemValTy mem,
                                        uint32_t align) {
  auto res = base().MemSet(BasePtrTy(std::move(ptr)), _val, len,
                           BaseMemValTy(std::move(mem)), align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::MemSet(OpSemWideMemManagerMixin::PtrTy ptr,
                                        Expr _val, unsigned int len,
                                        OpSemWideMemManagerMixin::MemValTy mem,
                                        uint32_t align) {
  auto res = base().MemSet(BasePtrTy(std::move(ptr)), _val, len,
                           BaseMemValTy(std::move(mem)), align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::storeValueToMem(
    Expr _val, OpSemWideMemManagerMixin::PtrTy ptr,
    OpSemWideMemManagerMixin::MemValTy memIn, const Type &ty, uint32_t align) {
  auto res = base().storeValueToMem(_val, BasePtrTy(std::move(ptr)),
                                    BaseMemValTy(std::move(memIn)), ty, align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::loadValueFromMem(
    OpSemWideMemManagerMixin::PtrTy ptr, OpSemWideMemManagerMixin::MemValTy mem,
    const Type &ty, uint64_t align) {
  auto res = base().loadValueFromMem(BasePtrTy(std::move(ptr)),
                                     BaseMemValTy(std::move(mem)), ty, align);
  return res;
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::storePtrToMem(
    OpSemWideMemManagerMixin::PtrTy val, OpSemWideMemManagerMixin::PtrTy ptr,
    OpSemWideMemManagerMixin::MemValTy mem, unsigned int byteSz,
    uint64_t align) {
  auto res = base().storePtrToMem(BasePtrTy(val), BasePtrTy(std::move(ptr)),
                                  BaseMemValTy(std::move(mem)), byteSz, align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemValTy
OpSemWideMemManagerMixin<BaseT>::storeIntToMem(
    Expr _val, OpSemWideMemManagerMixin::PtrTy ptr,
    OpSemWideMemManagerMixin::MemValTy mem, unsigned int byteSz,
    uint64_t align) {
  auto res = base().storeIntToMem(_val, BasePtrTy(std::move(ptr)),
                                  BaseMemValTy(std::move(mem)), byteSz, align);
  return toMemValTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::loadPtrFromMem(
    OpSemWideMemManagerMixin::PtrTy ptr, OpSemWideMemManagerMixin::MemValTy mem,
    unsigned int byteSz, uint64_t align) {
  auto res = base().loadPtrFromMem(BasePtrTy(std::move(ptr)),
                                   BaseMemValTy(std::move(mem)), byteSz, align);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::loadIntFromMem(
    OpSemWideMemManagerMixin::PtrTy ptr, OpSemWideMemManagerMixin::MemValTy mem,
    unsigned int byteSz, uint64_t align) {
  auto res = base().loadIntFromMem(BasePtrTy(std::move(ptr)),
                                   BaseMemValTy(std::move(mem)), byteSz, align);
  return res;
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::ptrAdd(OpSemWideMemManagerMixin::PtrTy ptr,
                                        int32_t _offset) const {
  auto res = base().ptrAdd(BasePtrTy(std::move(ptr)), _offset);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::ptrAdd(OpSemWideMemManagerMixin::PtrTy ptr,
                                        Expr offset) const {
  auto res = base().ptrAdd(BasePtrTy(std::move(ptr)), offset);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::coerce(Expr sort, Expr val) {
  return base().coerce(sort, val);
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::nullPtr() const {
  auto res = base().nullPtr();
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::freshPtr() {
  auto res = base().freshPtr();
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::MemSortTy
OpSemWideMemManagerMixin<BaseT>::mkMemRegisterSort(
    const Instruction &inst) const {
  auto res = base().mkMemRegisterSort(inst);
  return toMemSortTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrSortTy
OpSemWideMemManagerMixin<BaseT>::mkPtrRegisterSort(
    const GlobalVariable &gv) const {
  auto res = base().mkPtrRegisterSort(gv);
  return toPtrSortTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrSortTy
OpSemWideMemManagerMixin<BaseT>::mkPtrRegisterSort(const Function &fn) const {
  auto res = base().mkPtrRegisterSort(fn);
  return toPtrSortTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::getPtrToGlobalVariable(
    const GlobalVariable &gv) {
  auto res = base().getPtrToGlobalVariable(gv);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrSortTy
OpSemWideMemManagerMixin<BaseT>::mkPtrRegisterSort(
    const Instruction &inst) const {
  auto res = base().mkPtrRegisterSort(inst);
  return toPtrSortTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::mkAlignedPtr(Expr name, uint32_t align) const {
  auto res = base().mkAlignedPtr(name, align);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
void OpSemWideMemManagerMixin<BaseT>::initGlobalVariable(
    const GlobalVariable &gv) const {
  base().initGlobalVariable(gv);
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::getPtrToFunction(const Function &F) {
  auto res = base().getPtrToFunction(F);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::falloc(const Function &fn) {
  auto res = base().falloc(fn);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::galloc(const GlobalVariable &gv,
                                        uint32_t align) {
  auto res = base().galloc(gv, align);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::halloc(Expr bytes, uint32_t align) {
  auto res = base().halloc(bytes, align);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::halloc(unsigned int _bytes, uint32_t align) {
  auto res = base().halloc(_bytes, align);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::brk0Ptr() {
  auto res = base().brk0Ptr();
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::mkStackPtr(unsigned int offset) {
  auto res = base().mkStackPtr(offset);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
Expr OpSemWideMemManagerMixin<BaseT>::getFatData(
    OpSemWideMemManagerMixin::PtrTy p, unsigned int SlotIdx) {
  LOG("opsem", WARN << "getFatData() not implemented!\n");
  return Expr();
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::salloc(Expr elmts, unsigned int typeSz,
                                        uint32_t align) {
  auto res = base().salloc(elmts, typeSz, align);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrTy
OpSemWideMemManagerMixin<BaseT>::salloc(unsigned int bytes, uint32_t align) {
  auto res = base().salloc(bytes, align);
  return toPtrTy(std::move(res));
}
template <typename BaseT>
typename OpSemWideMemManagerMixin<BaseT>::PtrSortTy
OpSemWideMemManagerMixin<BaseT>::ptrSort() const {
  auto res = base().ptrSort();
  return toPtrSortTy(std::move(res));
}

template class OpSemWideMemManagerMixin<WideMemManager>;
template class OpSemWideMemManagerMixin<
    ExtraWideMemManager<OpSemWideMemManagerMixin<TrackingRawMemManager>>>;
template class OpSemWideMemManagerMixin<ExtraWideMemManager<RawMemManager>>;
template class OpSemWideMemManagerMixin<TrackingRawMemManager>;

} // namespace details
} // namespace seahorn
