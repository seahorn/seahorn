#include "BvOpSem2TrackingRawMemMgr.hh"

namespace seahorn {
namespace details {

static const unsigned int g_MetadataBitWidth = 8;
static const unsigned int g_MetadataByteWidth = g_MetadataBitWidth / 8;
static const unsigned int g_num_slots = 2;

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_metadata(sem, ctx, ptrSz, g_MetadataByteWidth, useLambdas, true) {}

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas,
                                             bool ignoreAlignment)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas, ignoreAlignment),
      m_metadata(sem, ctx, ptrSz, g_MetadataByteWidth, useLambdas, true) {}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::getAddressable(TrackingRawMemManager::PtrTy p) const {
  return p;
}

bool TrackingRawMemManager::isPtrTyVal(Expr e) const {
  // same PtrTy as RawMemManager
  return !e || !strct::isStructVal(e);
}

Expr TrackingRawMemManager::isDereferenceable(TrackingRawMemManager::PtrTy p,
                                              Expr byteSz) {
  // isDereferenceable should never be called in a 'RawMemMgr'
  return m_ctx.alu().getFalse();
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::zeroedMemory() const {
  return MemValTy(m_main.zeroedMemory(), m_metadata.zeroedMemory());
}
std::pair<char *, unsigned int>
TrackingRawMemManager::getGlobalVariableInitValue(const GlobalVariable &gv) {
  return m_main.getGlobalVariableInitValue(gv);
}
void TrackingRawMemManager::dumpGlobalsMap() { m_main.dumpGlobalsMap(); }
void TrackingRawMemManager::onFunctionEntry(const Function &fn) {
  m_main.onFunctionEntry(fn);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::gep(TrackingRawMemManager::PtrTy ptr,
                           gep_type_iterator it, gep_type_iterator end) const {
  return m_main.gep(ptr, it, end);
}
Expr TrackingRawMemManager::ptrEq(TrackingRawMemManager::PtrTy p1,
                                  TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrEq(p1, p2);
}
Expr TrackingRawMemManager::ptrtoint(TrackingRawMemManager::PtrTy ptr,
                                     const Type &ptrTy,
                                     const Type &intTy) const {
  return m_main.ptrtoint(ptr, ptrTy, intTy);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::inttoptr(Expr intVal, const Type &intTy,
                                const Type &ptrTy) const {
  return m_main.inttoptr(intVal, intTy, ptrTy);
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemFill(
    TrackingRawMemManager::PtrTy dPtr, char *sPtr, unsigned int len,
    TrackingRawMemManager::MemValTy mem, uint32_t align) {
  RawMemValTy rawVal = m_main.MemFill(dPtr, sPtr, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata());
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemCpy(
    TrackingRawMemManager::PtrTy dPtr, TrackingRawMemManager::PtrTy sPtr,
    Expr len, TrackingRawMemManager::MemValTy memTrsfrRead,
    TrackingRawMemManager::MemValTy memRead, uint32_t align) {
  RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                     memRead.getRaw(), align);
  return MemValTy(rawVal, memRead.getMetadata());
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemCpy(
    TrackingRawMemManager::PtrTy dPtr, TrackingRawMemManager::PtrTy sPtr,
    unsigned int len, TrackingRawMemManager::MemValTy memTrsfrRead,
    TrackingRawMemManager::MemValTy memRead, uint32_t align) {
  RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                     memRead.getRaw(), align);
  return MemValTy(rawVal, memRead.getMetadata());
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::MemSet(TrackingRawMemManager::PtrTy ptr, Expr _val,
                              Expr len, TrackingRawMemManager::MemValTy mem,
                              uint32_t align) {
  RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata());
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemSet(
    TrackingRawMemManager::PtrTy ptr, Expr _val, unsigned int len,
    TrackingRawMemManager::MemValTy mem, uint32_t align) {
  RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata());
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::storeValueToMem(
    Expr _val, TrackingRawMemManager::PtrTy ptr,
    TrackingRawMemManager::MemValTy memIn, const Type &ty, uint32_t align) {
  assert(ptr);
  Expr val = _val;
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr->efac();
  // TODO: use zeroed memory on m_main, m_metadata instead of explicit
  // init
  MemValTy res(m_ctx.alu().ui(0UL, wordSizeInBits()),
               m_ctx.alu().ui(0UL, g_MetadataBitWidth));
  switch (ty.getTypeID()) {
  case Type::IntegerTyID:
    if (ty.getScalarSizeInBits() < byteSz * 8) {
      val = m_ctx.alu().doZext(val, byteSz * 8, ty.getScalarSizeInBits());
    }
    res = storeIntToMem(val, ptr, memIn, byteSz, align);
    break;
  case Type::FloatTyID:
  case Type::DoubleTyID:
  case Type::X86_FP80TyID:
    errs() << "Error: store of float/double is not supported\n";
    llvm_unreachable(nullptr);
    break;
  case Type::VectorTyID:
    errs() << "Error: store of vectors is not supported\n";
  case Type::PointerTyID:
    res = storePtrToMem(val, ptr, memIn, byteSz, align);
    break;
  case Type::StructTyID:
    WARN << "Storing struct type " << ty << " is not supported\n";
    return res;
  default:
    SmallString<256> msg;
    raw_svector_ostream out(msg);
    out << "Loading from type: " << ty << " is not supported\n";
    assert(false);
  }
  return res;
}
Expr TrackingRawMemManager::loadValueFromMem(
    TrackingRawMemManager::PtrTy ptr, TrackingRawMemManager::MemValTy mem,
    const Type &ty, uint64_t align) {
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr->efac();

  Expr res;
  switch (ty.getTypeID()) {
  case Type::IntegerTyID:
    res = loadIntFromMem(ptr, mem, byteSz, align);
    if (res && ty.getScalarSizeInBits() < byteSz * 8)
      res = m_ctx.alu().doTrunc(res, ty.getScalarSizeInBits());
    break;
  case Type::FloatTyID:
  case Type::DoubleTyID:
  case Type::X86_FP80TyID:
    errs() << "Error: load of float/double is not supported\n";
    llvm_unreachable(nullptr);
    break;
  case Type::VectorTyID:
    errs() << "Error: load of vectors is not supported\n";
  case Type::PointerTyID:
    res = loadPtrFromMem(ptr, mem, byteSz, align);
    break;
  case Type::StructTyID:
    WARN << "loading form struct type " << ty << " is not supported";
    return res;
  default:
    SmallString<256> msg;
    raw_svector_ostream out(msg);
    out << "Loading from type: " << ty << " is not supported\n";
    assert(false);
  }
  return res;
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::storePtrToMem(
    TrackingRawMemManager::PtrTy val, TrackingRawMemManager::PtrTy ptr,
    TrackingRawMemManager::MemValTy mem, unsigned int byteSz, uint64_t align) {
  RawMemValTy rawVal =
      m_main.storePtrToMem(val, ptr, mem.getRaw(), byteSz, align);
  return MemValTy(rawVal, mem.getMetadata());
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::storeIntToMem(
    Expr _val, TrackingRawMemManager::PtrTy ptr,
    TrackingRawMemManager::MemValTy mem, unsigned int byteSz, uint64_t align) {
  // We expect _val to be a primitive rather than a container
  assert(!strct::isStructVal(_val));
  RawMemValTy rawVal =
      m_main.storeIntToMem(_val, ptr, mem.getRaw(), byteSz, align);
  return MemValTy(rawVal, mem.getMetadata());
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::loadPtrFromMem(TrackingRawMemManager::PtrTy ptr,
                                      TrackingRawMemManager::MemValTy mem,
                                      unsigned int byteSz, uint64_t align) {
  PtrTy rawPtr = m_main.loadPtrFromMem(ptr, mem.getRaw(), byteSz, align);
  return rawPtr;
}
Expr TrackingRawMemManager::loadIntFromMem(TrackingRawMemManager::PtrTy ptr,
                                           TrackingRawMemManager::MemValTy mem,
                                           unsigned int byteSz,
                                           uint64_t align) {
  Expr res = m_main.loadIntFromMem(ptr, mem.getRaw(), byteSz, align);
  return res;
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::memsetMetaData(PtrTy ptr, Expr len, MemValTy memIn,
                                      unsigned int val) {
  // make sure we can fit the supplied value in metadata memory slot
  assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth);
  return MemValTy(
      memIn.getRaw(),
      m_metadata.MemSet(ptr, m_ctx.alu().ui(val, g_MetadataBitWidth), len,
                        memIn.getMetadata(), m_metadata.wordSzInBytes()));
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::memsetMetaData(PtrTy ptr, unsigned int len,
                                      MemValTy memIn, unsigned int val) {
  // make sure we can fit the supplied value in metadata memory slot
  assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth);
  return MemValTy(
      memIn.getRaw(),
      m_metadata.MemSet(ptr, m_ctx.alu().ui(val, g_MetadataBitWidth), len,
                        memIn.getMetadata(), m_metadata.wordSzInBytes()));
}
Expr TrackingRawMemManager::getMetaData(PtrTy ptr, MemValTy memIn,
                                        unsigned int byteSz) {
  return m_metadata.loadIntFromMem(ptr, memIn.getMetadata(), byteSz,
                                   0 /* TODO: fix */);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::ptrAdd(TrackingRawMemManager::PtrTy ptr,
                              Expr offset) const {
  return m_main.ptrAdd(ptr, offset);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::ptrAdd(TrackingRawMemManager::PtrTy ptr,
                              int32_t _offset) const {
  return m_main.ptrAdd(ptr, _offset);
}
Expr TrackingRawMemManager::coerce(Expr sort, Expr val) {
  if (strct::isStructVal(val)) {
    llvm::SmallVector<Expr, g_num_slots> kids;
    assert(isOp<STRUCT_TY>(sort));
    assert(sort->arity() == val->arity());
    assert(sort->arity() == g_num_slots);
    kids.push_back(m_main.coerce(sort->arg(0), val->arg(0)));
    // when havocing a value; don't havoc(ignore) value for metadata memory,
    // instead use 'zeroed' memory.
    kids.push_back(m_metadata.zeroedMemory());
    return strct::mk(kids);
  }
  return m_main.coerce(sort, val);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::nullPtr() const {
  return m_main.nullPtr();
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::freshPtr() {
  return m_main.freshPtr();
}
TrackingRawMemManager::MemSortTy
TrackingRawMemManager::mkMemRegisterSort(const Instruction &inst) const {
  return MemSortTy(m_main.mkMemRegisterSort(inst),
                   m_metadata.mkMemRegisterSort(inst));
}
TrackingRawMemManager::PtrSortTy
TrackingRawMemManager::mkPtrRegisterSort(const GlobalVariable &gv) const {
  return m_main.mkPtrRegisterSort(gv);
}
TrackingRawMemManager::PtrSortTy
TrackingRawMemManager::mkPtrRegisterSort(const Function &fn) const {
  return m_main.mkPtrRegisterSort(fn);
}
TrackingRawMemManager::PtrSortTy
TrackingRawMemManager::mkPtrRegisterSort(const Instruction &inst) const {
  return m_main.mkPtrRegisterSort(inst);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::mkAlignedPtr(Expr name, uint32_t align) const {
  return m_main.mkAlignedPtr(name, align);
}
void TrackingRawMemManager::initGlobalVariable(const GlobalVariable &gv) const {
  return m_main.initGlobalVariable(gv);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::getPtrToGlobalVariable(const GlobalVariable &gv) {
  return m_main.getPtrToGlobalVariable(gv);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::falloc(const Function &fn) {
  return m_main.falloc(fn);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::galloc(const GlobalVariable &gv, uint32_t align) {
  return m_main.galloc(gv, align);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::halloc(Expr bytes,
                                                           uint32_t align) {
  return m_main.halloc(bytes, align);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::halloc(unsigned int _bytes,
                                                           uint32_t align) {
  return m_main.halloc(_bytes, align);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::salloc(unsigned int bytes,
                                                           uint32_t align) {
  return m_main.salloc(bytes, align);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::getPtrToFunction(const Function &F) {
  return m_main.getPtrToFunction(F);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::salloc(Expr elmts, unsigned int typeSz, uint32_t align) {
  return m_main.salloc(elmts, typeSz, align);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::mkStackPtr(unsigned int offset) {
  return m_main.mkStackPtr(offset);
}
unsigned int TrackingRawMemManager::getMetaDataMemWordSzInBits() {
  return m_metadata.wordSzInBits();
}
Expr TrackingRawMemManager::isModified(PtrTy p, MemValTy mem) {
  LOG("opsem", WARN << "isModified() not implemented!\n");
  return Expr();
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::resetModified(TrackingRawMemManager::PtrTy p,
                                     TrackingRawMemManager::MemValTy mem) {
  LOG("opsem", WARN << "resetModified() not implemented!\n");
  return mem;
}
Expr TrackingRawMemManager::ptrUlt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrUlt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSlt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrSlt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrUle(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrUle(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSle(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrSle(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrUgt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrUgt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSgt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrSgt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrUge(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrUge(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSge(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return expr::Expr();
}
Expr TrackingRawMemManager::ptrNe(TrackingRawMemManager::PtrTy p1,
                                  TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrNe(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSub(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return m_main.ptrSub(getAddressable(p1), getAddressable(p2));
}
} // namespace details
} // namespace seahorn
