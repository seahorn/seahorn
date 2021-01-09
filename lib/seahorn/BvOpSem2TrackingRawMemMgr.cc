#include "BvOpSem2TrackingRawMemMgr.hh"

namespace seahorn {
namespace details {

const unsigned int TrackingRawMemManager::g_MetadataBitWidth = 8;
const unsigned int TrackingRawMemManager::g_MetadataByteWidth =
    TrackingRawMemManager::g_MetadataBitWidth / 8;
const unsigned int TrackingRawMemManager::g_num_slots = 4;

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_w_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_r_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_a_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true) {
  m_metadata_map = {
      {MetadataKind::READ, &m_r_metadata},
      {MetadataKind::WRITE, &m_w_metadata},
      {MetadataKind::ALLOC, &m_a_metadata},
  };
}

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas,
                                             bool ignoreAlignment)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas, ignoreAlignment),
      m_w_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_r_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_a_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true) {
  m_metadata_map = {
      {MetadataKind::READ, &m_r_metadata},
      {MetadataKind::WRITE, &m_w_metadata},
      {MetadataKind::ALLOC, &m_a_metadata},
  };
}

TrackingRawMemManager::PtrTy
TrackingRawMemManager::getAddressable(TrackingRawMemManager::PtrTy p) const {
  return p;
}

bool TrackingRawMemManager::isPtrTyVal(Expr e) const {
  // same PtrTy as RawMemManager
  return e && !strct::isStructVal(e);
}

bool TrackingRawMemManager::isMemVal(Expr e) const {
  // raw and metadata
  return e && strct::isStructVal(e) && e->arity() == g_num_slots;
}

Expr TrackingRawMemManager::isDereferenceable(TrackingRawMemManager::PtrTy p,
                                              Expr byteSz) {
  // isDereferenceable should never be called in a 'RawMemMgr'
  return m_ctx.alu().getFalse();
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::zeroedMemory() const {
  return MemValTy(m_main.zeroedMemory(),
                  m_metadata_map.at(MetadataKind::READ)->zeroedMemory(),
                  m_metadata_map.at(MetadataKind::WRITE)->zeroedMemory(),
                  m_metadata_map.at(MetadataKind::ALLOC)->zeroedMemory());
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
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemCpy(
    TrackingRawMemManager::PtrTy dPtr, TrackingRawMemManager::PtrTy sPtr,
    Expr len, TrackingRawMemManager::MemValTy memTrsfrRead,
    TrackingRawMemManager::MemValTy memRead, uint32_t align) {
  RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                     memRead.getRaw(), align);
  return MemValTy(rawVal, memRead.getMetadata(MetadataKind::READ),
                  memRead.getMetadata(MetadataKind::WRITE),
                  memRead.getMetadata(MetadataKind::ALLOC));
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemCpy(
    TrackingRawMemManager::PtrTy dPtr, TrackingRawMemManager::PtrTy sPtr,
    unsigned int len, TrackingRawMemManager::MemValTy memTrsfrRead,
    TrackingRawMemManager::MemValTy memRead, uint32_t align) {
  RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                     memRead.getRaw(), align);
  return MemValTy(rawVal, memRead.getMetadata(MetadataKind::READ),
                  memRead.getMetadata(MetadataKind::WRITE),
                  memRead.getMetadata(MetadataKind::ALLOC));
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::MemSet(TrackingRawMemManager::PtrTy ptr, Expr _val,
                              Expr len, TrackingRawMemManager::MemValTy mem,
                              uint32_t align) {
  RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemSet(
    TrackingRawMemManager::PtrTy ptr, Expr _val, unsigned int len,
    TrackingRawMemManager::MemValTy mem, uint32_t align) {
  RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}

// TODO: refactor this dispatch function in Mixin class
TrackingRawMemManager::MemValTy TrackingRawMemManager::storeValueToMem(
    Expr _val, TrackingRawMemManager::PtrTy ptr,
    TrackingRawMemManager::MemValTy memIn, const Type &ty, uint32_t align) {
  assert(ptr);
  Expr val = _val;
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr->efac();
  MemValTy res = MemValTy(Expr());
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
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::storeIntToMem(
    Expr _val, TrackingRawMemManager::PtrTy ptr,
    TrackingRawMemManager::MemValTy mem, unsigned int byteSz, uint64_t align) {
  // We expect _val to be a primitive rather than a container
  assert(!strct::isStructVal(_val));
  RawMemValTy rawVal =
      m_main.storeIntToMem(_val, ptr, mem.getRaw(), byteSz, align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
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
TrackingRawMemManager::memsetMetaData(MetadataKind kind, PtrTy ptr, Expr len,
                                      MemValTy memIn, unsigned int val) {
  // make sure we can fit the supplied value in metadata memory slot
  assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth &&
         "Metadata cannot fit!");
  return MemValTy(
      kind, memIn,
      m_metadata_map[kind]->MemSet(ptr, m_ctx.alu().ui(val, g_MetadataBitWidth),
                                   len, memIn.getMetadata(kind),
                                   m_metadata_map[kind]->wordSzInBytes()));
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::memsetMetaData(MetadataKind kind, PtrTy ptr,
                                      unsigned int len, MemValTy memIn,
                                      unsigned int val) {
  // make sure we can fit the supplied value in metadata memory slot
  assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth &&
         "Metadata cannot fit!");
  return MemValTy(
      kind, memIn,
      m_metadata_map[kind]->MemSet(ptr, m_ctx.alu().ui(val, g_MetadataBitWidth),
                                   len, memIn.getMetadata(kind),
                                   m_metadata_map[kind]->wordSzInBytes()));
}
Expr TrackingRawMemManager::getMetaData(MetadataKind kind, PtrTy ptr,
                                        MemValTy memIn, unsigned int byteSz) {
  // TODO: expose a method in OpSemMemManager to loadAlignedWordFromMem
  return m_metadata_map.at(kind)->loadIntFromMem(
      ptr, memIn.getMetadata(kind), byteSz,
      m_metadata_map.at(kind)->wordSizeInBytes());
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
    // instead intialize memory to a constant value.
    kids.push_back(m_metadata_map.at(MetadataKind::READ)->zeroedMemory());
    kids.push_back(m_metadata_map.at(MetadataKind::WRITE)->zeroedMemory());
    kids.push_back(m_metadata_map.at(MetadataKind::ALLOC)->zeroedMemory());
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
  return MemSortTy(
      m_main.mkMemRegisterSort(inst),
      m_metadata_map.at(MetadataKind::READ)->mkMemRegisterSort(inst),
      m_metadata_map.at(MetadataKind::WRITE)->mkMemRegisterSort(inst),
      m_metadata_map.at(MetadataKind::ALLOC)->mkMemRegisterSort(inst));
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
  assert(m_metadata_map.at(MetadataKind::READ)->wordSzInBits() ==
         m_metadata_map.at(MetadataKind::WRITE)->wordSzInBits());
  assert(m_metadata_map.at(MetadataKind::READ)->wordSzInBits() ==
         m_metadata_map.at(MetadataKind::ALLOC)->wordSzInBits());
  return m_metadata_map.at(MetadataKind::READ)->wordSzInBits();
}
Expr TrackingRawMemManager::isMetadataSet(MetadataKind kind, PtrTy p,
                                          MemValTy mem) {
  LOG("opsem", ERR << "isMetadataSet() not implemented!\n");
  return Expr();
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::setMetadata(
    MetadataKind kind, TrackingRawMemManager::PtrTy p,
    TrackingRawMemManager::MemValTy mem, unsigned val) {
  LOG("opsem", ERR << "setMetadata() not implemented!\n");
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
