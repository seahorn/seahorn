#include "BvOpSem2TrackingRawMemMgr.hh"

namespace seahorn {
namespace details {

template <class T>
const unsigned int TrackingMemManagerCore<T>::g_MetadataBitWidth = 8;

template <class T>
const unsigned int TrackingMemManagerCore<T>::g_MetadataByteWidth =
    TrackingRawMemManager::g_MetadataBitWidth / 8;

template <class T>
const unsigned int TrackingMemManagerCore<T>::g_num_slots = 4;

template <class T>
TrackingMemManagerCore<T>::TrackingMemManagerCore(Bv2OpSem &sem,
                                                  Bv2OpSemContext &ctx,
                                                  unsigned ptrSz,
                                                  unsigned wordSz,
                                                  bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_w_metadata(sem, ctx, ptrSz, TrackingMemManagerCore::g_MetadataByteWidth,
                   useLambdas, true),
      m_r_metadata(sem, ctx, ptrSz, TrackingMemManagerCore::g_MetadataByteWidth,
                   useLambdas, true),
      m_a_metadata(sem, ctx, ptrSz, TrackingMemManagerCore::g_MetadataByteWidth,
                   useLambdas, true) {
  m_metadata_map = {
      {MetadataKind::READ, &m_r_metadata},
      {MetadataKind::WRITE, &m_w_metadata},
      {MetadataKind::ALLOC, &m_a_metadata},
  };
  // Currently, we only support RawMemManagerCore or subclasses of it.
  static_assert(std::is_base_of<OpSemMemManagerBase, T>::value,
                "T not derived from OpSemMemManagerBase");
}

template <class T>
TrackingMemManagerCore<T>::TrackingMemManagerCore(
    Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz, unsigned wordSz,
    bool useLambdas, bool ignoreAlignment)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas, ignoreAlignment),
      m_w_metadata(sem, ctx, ptrSz,
                   TrackingMemManagerCore<T>::g_MetadataByteWidth, useLambdas,
                   true),
      m_r_metadata(sem, ctx, ptrSz,
                   TrackingMemManagerCore<T>::g_MetadataByteWidth, useLambdas,
                   true),
      m_a_metadata(sem, ctx, ptrSz,
                   TrackingMemManagerCore<T>::g_MetadataByteWidth, useLambdas,
                   true) {
  m_metadata_map = {
      {MetadataKind::READ, &m_r_metadata},
      {MetadataKind::WRITE, &m_w_metadata},
      {MetadataKind::ALLOC, &m_a_metadata},
  };
  // Currently, we only support RawMemManagerCore or subclasses of it.
  static_assert(std::is_base_of<OpSemMemManagerBase, T>::value,
                "T not derived from OpSemMemManagerBase");
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::getAddressable(PtrTy p) const {
  return p;
}

template <class T> bool TrackingMemManagerCore<T>::isPtrTyVal(Expr e) const {
  // same PtrTy as RawMemManager
  return e && !strct::isStructVal(e);
}

template <class T> bool TrackingMemManagerCore<T>::isMemVal(Expr e) const {
  // raw and metadata
  return e && strct::isStructVal(e) && e->arity() == g_num_slots;
}

template <class T>
Expr TrackingMemManagerCore<T>::isDereferenceable(PtrTy p, Expr byteSz) {
  // isDereferenceable should never be called in a 'RawMemMgr'
  return m_ctx.alu().getFalse();
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::zeroedMemory() const {
  return MemValTy(m_main.zeroedMemory(),
                  m_metadata_map.at(MetadataKind::READ)->zeroedMemory(),
                  m_metadata_map.at(MetadataKind::WRITE)->zeroedMemory(),
                  m_metadata_map.at(MetadataKind::ALLOC)->zeroedMemory());
}

template <class T>
std::pair<char *, unsigned int>
TrackingMemManagerCore<T>::getGlobalVariableInitValue(
    const GlobalVariable &gv) {
  return m_main.getGlobalVariableInitValue(gv);
}

template <class T> void TrackingMemManagerCore<T>::dumpGlobalsMap() {
  m_main.dumpGlobalsMap();
}

template <class T>
void TrackingMemManagerCore<T>::onFunctionEntry(const Function &fn) {
  m_main.onFunctionEntry(fn);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::gep(PtrTy ptr, gep_type_iterator it,
                               gep_type_iterator end) const {
  return m_main.gep(ptr, it, end);
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrEq(PtrTy p1, PtrTy p2) const {
  return m_main.ptrEq(p1, p2);
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrtoint(PtrTy ptr, const Type &ptrTy,
                                         const Type &intTy) const {
  return m_main.ptrtoint(ptr, ptrTy, intTy);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::inttoptr(Expr intVal, const Type &intTy,
                                    const Type &ptrTy) const {
  return m_main.inttoptr(intVal, intTy, ptrTy);
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::MemFill(PtrTy dPtr, char *sPtr, unsigned int len,
                                   MemValTy mem, uint32_t align) {
  RawMemValTy rawVal = m_main.MemFill(dPtr, sPtr, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len,
                                  MemValTy memTrsfrRead, MemValTy memRead,
                                  uint32_t align) {
  RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                     memRead.getRaw(), align);
  return MemValTy(rawVal, memRead.getMetadata(MetadataKind::READ),
                  memRead.getMetadata(MetadataKind::WRITE),
                  memRead.getMetadata(MetadataKind::ALLOC));
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned int len,
                                  MemValTy memTrsfrRead, MemValTy memRead,
                                  uint32_t align) {
  RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                     memRead.getRaw(), align);
  return MemValTy(rawVal, memRead.getMetadata(MetadataKind::READ),
                  memRead.getMetadata(MetadataKind::WRITE),
                  memRead.getMetadata(MetadataKind::ALLOC));
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                                  uint32_t align) {
  RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::MemSet(PtrTy ptr, Expr _val, unsigned int len,
                                  MemValTy mem, uint32_t align) {
  RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}

// TODO: refactor this dispatch function in Mixin class
template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn,
                                           const Type &ty, uint32_t align) {
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

template <class T>
Expr TrackingMemManagerCore<T>::loadValueFromMem(PtrTy ptr, MemValTy mem,
                                                 const Type &ty,
                                                 uint64_t align) {
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

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                                         unsigned int byteSz, uint64_t align) {
  RawMemValTy rawVal =
      m_main.storePtrToMem(val, ptr, mem.getRaw(), byteSz, align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                                         unsigned int byteSz, uint64_t align) {
  // We expect _val to be a primitive rather than a container
  assert(!strct::isStructVal(_val));
  RawMemValTy rawVal =
      m_main.storeIntToMem(_val, ptr, mem.getRaw(), byteSz, align);
  return MemValTy(rawVal, mem.getMetadata(MetadataKind::READ),
                  mem.getMetadata(MetadataKind::WRITE),
                  mem.getMetadata(MetadataKind::ALLOC));
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::loadPtrFromMem(PtrTy ptr, MemValTy mem,
                                          unsigned int byteSz, uint64_t align) {
  PtrTy rawPtr = m_main.loadPtrFromMem(ptr, mem.getRaw(), byteSz, align);
  return rawPtr;
}

template <class T>
Expr TrackingMemManagerCore<T>::loadIntFromMem(PtrTy ptr, MemValTy mem,
                                               unsigned int byteSz,
                                               uint64_t align) {
  Expr res = m_main.loadIntFromMem(ptr, mem.getRaw(), byteSz, align);
  return res;
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::memsetMetaData(MetadataKind kind, PtrTy ptr,
                                          Expr len, MemValTy memIn,
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

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::memsetMetaData(MetadataKind kind, PtrTy ptr,
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

template <class T>
Expr TrackingMemManagerCore<T>::getMetaData(MetadataKind kind, PtrTy ptr,
                                            MemValTy memIn,
                                            unsigned int byteSz) {
  // TODO: expose a method in OpSemMemManager to loadAlignedWordFromMem
  return m_metadata_map.at(kind)->loadIntFromMem(
      ptr, memIn.getMetadata(kind), byteSz,
      m_metadata_map.at(kind)->wordSizeInBytes());
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::ptrAdd(TrackingMemManagerCore<T>::PtrTy ptr,
                                  Expr offset) const {
  return m_main.ptrAdd(ptr, offset);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::ptrAdd(TrackingMemManagerCore<T>::PtrTy ptr,
                                  int32_t _offset) const {
  return m_main.ptrAdd(ptr, _offset);
}

template <class T> Expr TrackingMemManagerCore<T>::coerce(Expr sort, Expr val) {
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

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::nullPtr() const {
  return m_main.nullPtr();
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::freshPtr() {
  return m_main.freshPtr();
}

template <class T>
typename TrackingMemManagerCore<T>::MemSortTy
TrackingMemManagerCore<T>::mkMemRegisterSort(const Instruction &inst) const {
  return MemSortTy(
      m_main.mkMemRegisterSort(inst),
      m_metadata_map.at(MetadataKind::READ)->mkMemRegisterSort(inst),
      m_metadata_map.at(MetadataKind::WRITE)->mkMemRegisterSort(inst),
      m_metadata_map.at(MetadataKind::ALLOC)->mkMemRegisterSort(inst));
}

template <class T>
typename TrackingMemManagerCore<T>::PtrSortTy
TrackingMemManagerCore<T>::mkPtrRegisterSort(const GlobalVariable &gv) const {
  return m_main.mkPtrRegisterSort(gv);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrSortTy
TrackingMemManagerCore<T>::mkPtrRegisterSort(const Function &fn) const {
  return m_main.mkPtrRegisterSort(fn);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrSortTy
TrackingMemManagerCore<T>::mkPtrRegisterSort(const Instruction &inst) const {
  return m_main.mkPtrRegisterSort(inst);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::mkAlignedPtr(Expr name, uint32_t align) const {
  return m_main.mkAlignedPtr(name, align);
}

template <class T>
void TrackingMemManagerCore<T>::initGlobalVariable(
    const GlobalVariable &gv) const {
  return m_main.initGlobalVariable(gv);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::getPtrToGlobalVariable(const GlobalVariable &gv) {
  return m_main.getPtrToGlobalVariable(gv);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::falloc(const Function &fn) {
  return m_main.falloc(fn);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::galloc(const GlobalVariable &gv, uint32_t align) {
  return m_main.galloc(gv, align);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::halloc(Expr bytes, uint32_t align) {
  return m_main.halloc(bytes, align);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::halloc(unsigned int _bytes, uint32_t align) {
  return m_main.halloc(_bytes, align);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::salloc(unsigned int bytes, uint32_t align) {
  return m_main.salloc(bytes, align);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::getPtrToFunction(const Function &F) {
  return m_main.getPtrToFunction(F);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::salloc(Expr elmts, unsigned int typeSz,
                                  uint32_t align) {
  return m_main.salloc(elmts, typeSz, align);
}

template <class T>
typename TrackingMemManagerCore<T>::PtrTy
TrackingMemManagerCore<T>::mkStackPtr(unsigned int offset) {
  return m_main.mkStackPtr(offset);
}

template <class T>
unsigned int TrackingMemManagerCore<T>::getMetaDataMemWordSzInBits() {
  assert(m_metadata_map.at(MetadataKind::READ)->wordSzInBits() ==
         m_metadata_map.at(MetadataKind::WRITE)->wordSzInBits());
  assert(m_metadata_map.at(MetadataKind::READ)->wordSzInBits() ==
         m_metadata_map.at(MetadataKind::ALLOC)->wordSzInBits());
  return m_metadata_map.at(MetadataKind::READ)->wordSzInBits();
}

template <class T>
Expr TrackingMemManagerCore<T>::isMetadataSet(MetadataKind kind, PtrTy p,
                                              MemValTy mem) {
  LOG("opsem", ERR << "isMetadataSet() not implemented!\n");
  return Expr();
}

template <class T>
typename TrackingMemManagerCore<T>::MemValTy
TrackingMemManagerCore<T>::setMetadata(MetadataKind kind,
                                       TrackingMemManagerCore<T>::PtrTy p,
                                       TrackingMemManagerCore<T>::MemValTy mem,
                                       unsigned val) {
  LOG("opsem", ERR << "setMetadata() not implemented!\n");
  return mem;
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrUlt(TrackingMemManagerCore::PtrTy p1,
                                       TrackingMemManagerCore::PtrTy p2) const {
  return m_main.ptrUlt(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrSlt(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrSlt(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrUle(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrUle(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrSle(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrSle(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrUgt(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrUgt(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrSgt(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrSgt(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrUge(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrUge(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrSge(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return expr::Expr();
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrNe(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrNe(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr TrackingMemManagerCore<T>::ptrSub(
    TrackingMemManagerCore<T>::PtrTy p1,
    TrackingMemManagerCore<T>::PtrTy p2) const {
  return m_main.ptrSub(getAddressable(p1), getAddressable(p2));
}
OpSemMemManager *mkTrackingRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                         unsigned int ptrSz,
                                         unsigned int wordSz, bool useLambdas) {
  return new TrackingRawMemManager(sem, ctx, ptrSz, wordSz, useLambdas);
}

template class TrackingMemManagerCore<RawMemManager>;

} // namespace details
} // namespace seahorn
