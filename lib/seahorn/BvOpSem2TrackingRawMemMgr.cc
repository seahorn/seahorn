#include "BvOpSem2TrackingRawMemMgr.hh"

namespace seahorn {
namespace details {

const unsigned int TrackingRawMemManager::g_MetadataBitWidth = 8;
const unsigned int TrackingRawMemManager::g_MetadataByteWidth =
    TrackingRawMemManager::g_MetadataBitWidth / 8;
const unsigned int TrackingRawMemManager::g_num_slots =
    TrackingMemoryTuple::GetTupleSize();

TrackingMemoryTuple::TrackingMemoryTuple(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                         unsigned ptrSz, unsigned wordSz,
                                         bool useLambdas)
    : m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_w_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_r_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_a_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_c0_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                    useLambdas, true) {}

TrackingMemoryTuple::TrackingMemoryTuple(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                         unsigned ptrSz, unsigned wordSz,
                                         bool useLambdas, bool ignoreAlignment)
    : m_main(sem, ctx, ptrSz, wordSz, useLambdas, ignoreAlignment),
      m_w_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_r_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_a_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                   useLambdas, true),
      m_c0_metadata(sem, ctx, ptrSz, TrackingRawMemManager::g_MetadataByteWidth,
                    useLambdas, true) {}

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_submgrs(sem, ctx, ptrSz, wordSz, useLambdas) {}

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas,
                                             bool ignoreAlignment)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_submgrs(sem, ctx, ptrSz, wordSz, useLambdas, ignoreAlignment) {}

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
  auto x = hana::transform(hana::keys(m_submgrs), [&](auto key) {
    return hana::at_key(m_submgrs, key).zeroedMemory();
  });
  return MemValTy(x);
}

std::pair<char *, unsigned int>
TrackingRawMemManager::getGlobalVariableInitValue(const GlobalVariable &gv) {
  return MAIN_MEM_MGR.getGlobalVariableInitValue(gv);
}
void TrackingRawMemManager::dumpGlobalsMap() { MAIN_MEM_MGR.dumpGlobalsMap(); }
void TrackingRawMemManager::onFunctionEntry(const Function &fn) {
  MAIN_MEM_MGR.onFunctionEntry(fn);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::gep(TrackingRawMemManager::PtrTy ptr,
                           gep_type_iterator it, gep_type_iterator end) const {
  return MAIN_MEM_MGR.gep(ptr, it, end);
}
Expr TrackingRawMemManager::ptrEq(TrackingRawMemManager::PtrTy p1,
                                  TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrEq(p1, p2);
}
Expr TrackingRawMemManager::ptrtoint(TrackingRawMemManager::PtrTy ptr,
                                     const Type &ptrTy,
                                     const Type &intTy) const {
  return MAIN_MEM_MGR.ptrtoint(ptr, ptrTy, intTy);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::inttoptr(Expr intVal, const Type &intTy,
                                const Type &ptrTy) const {
  return MAIN_MEM_MGR.inttoptr(intVal, intTy, ptrTy);
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemFill(
    TrackingRawMemManager::PtrTy dPtr, char *sPtr, unsigned int len,
    TrackingRawMemManager::MemValTy mem, uint32_t align) {
  RawMemValTy rawVal =
      MAIN_MEM_MGR.MemFill(dPtr, sPtr, len, mem.getRaw(), align);
  auto c = hana::prepend(mem.tail(), rawVal);
  return MemValTy(c);
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemCpy(
    TrackingRawMemManager::PtrTy dPtr, TrackingRawMemManager::PtrTy sPtr,
    Expr len, TrackingRawMemManager::MemValTy memTrsfrRead,
    TrackingRawMemManager::MemValTy memRead, uint32_t align) {
  RawMemValTy rawVal = MAIN_MEM_MGR.MemCpy(
      dPtr, sPtr, len, memTrsfrRead.getRaw(), memRead.getRaw(), align);
  auto c = hana::prepend(memRead.tail(), rawVal);
  return MemValTy(c);
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemCpy(
    TrackingRawMemManager::PtrTy dPtr, TrackingRawMemManager::PtrTy sPtr,
    unsigned int len, TrackingRawMemManager::MemValTy memTrsfrRead,
    TrackingRawMemManager::MemValTy memRead, uint32_t align) {
  RawMemValTy rawVal = MAIN_MEM_MGR.MemCpy(
      dPtr, sPtr, len, memTrsfrRead.getRaw(), memRead.getRaw(), align);
  auto c = hana::prepend(memRead.tail(), rawVal);
  return MemValTy(c);
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::MemSet(TrackingRawMemManager::PtrTy ptr, Expr _val,
                              Expr len, TrackingRawMemManager::MemValTy mem,
                              uint32_t align) {
  RawMemValTy rawVal = MAIN_MEM_MGR.MemSet(ptr, _val, len, mem.getRaw(), align);
  auto c = hana::prepend(mem.tail(), rawVal);
  return MemValTy(c);
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::MemSet(
    TrackingRawMemManager::PtrTy ptr, Expr _val, unsigned int len,
    TrackingRawMemManager::MemValTy mem, uint32_t align) {
  RawMemValTy rawVal = MAIN_MEM_MGR.MemSet(ptr, _val, len, mem.getRaw(), align);
  auto c = hana::prepend(mem.tail(), rawVal);
  return MemValTy(c);
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
      MAIN_MEM_MGR.storePtrToMem(val, ptr, mem.getRaw(), byteSz, align);
  auto c = hana::prepend(mem.tail(), rawVal);
  return MemValTy(c);
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::storeIntToMem(
    Expr _val, TrackingRawMemManager::PtrTy ptr,
    TrackingRawMemManager::MemValTy mem, unsigned int byteSz, uint64_t align) {
  // We expect _val to be a primitive rather than a container
  assert(!strct::isStructVal(_val));
  RawMemValTy rawVal =
      MAIN_MEM_MGR.storeIntToMem(_val, ptr, mem.getRaw(), byteSz, align);
  auto c = hana::prepend(mem.tail(), rawVal);
  return MemValTy(c);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::loadPtrFromMem(TrackingRawMemManager::PtrTy ptr,
                                      TrackingRawMemManager::MemValTy mem,
                                      unsigned int byteSz, uint64_t align) {
  PtrTy rawPtr = MAIN_MEM_MGR.loadPtrFromMem(ptr, mem.getRaw(), byteSz, align);
  return rawPtr;
}
Expr TrackingRawMemManager::loadIntFromMem(TrackingRawMemManager::PtrTy ptr,
                                           TrackingRawMemManager::MemValTy mem,
                                           unsigned int byteSz,
                                           uint64_t align) {
  Expr res = MAIN_MEM_MGR.loadIntFromMem(ptr, mem.getRaw(), byteSz, align);
  return res;
}
// Note that the setMetadata and getMetadata functions, kind is not known at
// compile time because we can't use compile time constants across virtual
// functions. Thus, we need to check whether kind equals ith element for each i.
TrackingRawMemManager::MemValTy
TrackingRawMemManager::memsetMetadata(MetadataKind kind, PtrTy ptr, Expr len,
                                      MemValTy memIn, unsigned int val) {
  // make sure we can fit the supplied value in metadata memory slot
  assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth &&
         "Metadata cannot fit!");
  auto index = static_cast<size_t>(kind) + 1;
  auto r =
      hana::make_range(hana::size_c<0>, TrackingMemoryTuple::GetTupleSize());
  auto r_t = hana::to_tuple(r);
  auto c =
      hana::transform(hana::zip(r_t, hana::keys(m_submgrs)), [&](auto pair) {
        auto current = hana::at(pair, hana::size_c<0>);
        auto key = hana::at(pair, hana::size_c<1>);
        if (current == index) {
          return hana::at_key(m_submgrs, key)
              .MemSet(ptr, m_ctx.alu().ui(val, g_MetadataBitWidth), len,
                      memIn.getElementVal(index),
                      hana::at_key(m_submgrs, key).wordSzInBytes());
        } else {
          return memIn.getElementVal(current);
        }
      });
  return MemValTy(c);
}
TrackingRawMemManager::MemValTy
TrackingRawMemManager::memsetMetadata(MetadataKind kind, PtrTy ptr,
                                      unsigned int len, MemValTy memIn,
                                      unsigned int val) {
  // make sure we can fit the supplied value in metadata memory slot
  assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth &&
         "Metadata cannot fit!");
  auto index = static_cast<size_t>(kind) + 1;
  auto r =
      hana::make_range(hana::int_c<0>, TrackingMemoryTuple::GetTupleSize());
  auto r_t = hana::to_tuple(r);
  auto z_t = hana::zip(r_t, hana::keys(m_submgrs));
  auto c = hana::transform(z_t, [&](auto pair) {
    auto current = hana::at(pair, hana::size_c<0>);
    auto key = hana::at(pair, hana::size_c<1>);
    if (current == index) {
      return hana::at_key(m_submgrs, key)
          .MemSet(ptr, m_ctx.alu().ui(val, g_MetadataBitWidth), len,
                  memIn.getElementVal(index),
                  hana::at_key(m_submgrs, key).wordSzInBytes());
    } else {
      return memIn.getElementVal(current);
    }
  });
  return MemValTy(c);
}
Expr TrackingRawMemManager::getMetadata(MetadataKind kind, PtrTy ptr,
                                        MemValTy memIn, unsigned int byteSz) {
  // TODO: expose a method in OpSemMemManager to loadAlignedWordFromMem
  auto index = static_cast<size_t>(kind) + 1;
  auto r =
      hana::make_range(hana::int_c<0>, TrackingMemoryTuple::GetTupleSize());
  auto r_t = hana::to_tuple(r);
  Expr ret;
  hana::for_each(hana::zip(r_t, hana::keys(m_submgrs)), [&](auto pair) {
    auto current = hana::at(pair, hana::size_c<0>);
    auto key = hana::at(pair, hana::size_c<1>);
    if (current == index) {
      ret = hana::at_key(m_submgrs, key)
                .loadIntFromMem(ptr, memIn.getElementVal(current), byteSz,
                                hana::at_key(m_submgrs, key).wordSzInBytes());
    }
  });
  return ret;
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::ptrAdd(TrackingRawMemManager::PtrTy ptr,
                              Expr offset) const {
  return MAIN_MEM_MGR.ptrAdd(ptr, offset);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::ptrAdd(TrackingRawMemManager::PtrTy ptr,
                              int32_t _offset) const {
  return MAIN_MEM_MGR.ptrAdd(ptr, _offset);
}
Expr TrackingRawMemManager::coerce(Expr sort, Expr val) {
  if (strct::isStructVal(val)) {
    assert(isOp<STRUCT_TY>(sort));
    assert(sort->arity() == val->arity());
    assert(sort->arity() == g_num_slots);
    auto c = hana::transform(
        hana::slice_c<hana::size_c<1>, TrackingMemoryTuple::GetTupleSize()>(
            hana::keys(m_submgrs)),
        [&](auto key) { return hana::at_key(m_submgrs, key).zeroedMemory(); });
    auto r = hana::prepend(c, MAIN_MEM_MGR.coerce(sort->arg(0), val->arg(0)));
    BOOST_HANA_CONSTANT_ASSERT(hana::size(r) ==
                               TrackingMemoryTuple::GetTupleSize());
    auto a = hana::unpack(r, [](auto... i) {
      return std::array<RawMemValTy, sizeof...(i)>{{i...}};
    });
    return strct::mk(a);
  }
  return MAIN_MEM_MGR.coerce(sort, val);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::nullPtr() const {
  return MAIN_MEM_MGR.nullPtr();
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::freshPtr() {
  return MAIN_MEM_MGR.freshPtr();
}
TrackingRawMemManager::MemSortTy
TrackingRawMemManager::mkMemRegisterSort(const Instruction &inst) const {
  auto c = hana::transform(hana::keys(m_submgrs), [&](auto key) {
    return hana::at_key(m_submgrs, key).mkMemRegisterSort(inst);
  });
  return MemSortTy(c);
}
TrackingRawMemManager::PtrSortTy
TrackingRawMemManager::mkPtrRegisterSort(const GlobalVariable &gv) const {
  return MAIN_MEM_MGR.mkPtrRegisterSort(gv);
}
TrackingRawMemManager::PtrSortTy
TrackingRawMemManager::mkPtrRegisterSort(const Function &fn) const {
  return MAIN_MEM_MGR.mkPtrRegisterSort(fn);
}
TrackingRawMemManager::PtrSortTy
TrackingRawMemManager::mkPtrRegisterSort(const Instruction &inst) const {
  return MAIN_MEM_MGR.mkPtrRegisterSort(inst);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::mkAlignedPtr(Expr name, uint32_t align) const {
  return MAIN_MEM_MGR.mkAlignedPtr(name, align);
}
void TrackingRawMemManager::initGlobalVariable(const GlobalVariable &gv) const {
  return MAIN_MEM_MGR.initGlobalVariable(gv);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::getPtrToGlobalVariable(const GlobalVariable &gv) {
  return MAIN_MEM_MGR.getPtrToGlobalVariable(gv);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::falloc(const Function &fn) {
  return MAIN_MEM_MGR.falloc(fn);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::galloc(const GlobalVariable &gv, uint32_t align) {
  return MAIN_MEM_MGR.galloc(gv, align);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::halloc(Expr bytes,
                                                           uint32_t align) {
  return MAIN_MEM_MGR.halloc(bytes, align);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::halloc(unsigned int _bytes,
                                                           uint32_t align) {
  return MAIN_MEM_MGR.halloc(_bytes, align);
}
TrackingRawMemManager::PtrTy TrackingRawMemManager::salloc(unsigned int bytes,
                                                           uint32_t align) {
  return MAIN_MEM_MGR.salloc(bytes, align);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::getPtrToFunction(const Function &F) {
  return MAIN_MEM_MGR.getPtrToFunction(F);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::salloc(Expr elmts, unsigned int typeSz, uint32_t align) {
  return MAIN_MEM_MGR.salloc(elmts, typeSz, align);
}
TrackingRawMemManager::PtrTy
TrackingRawMemManager::mkStackPtr(unsigned int offset) {
  return MAIN_MEM_MGR.mkStackPtr(offset);
}
unsigned int TrackingRawMemManager::getMetadataMemWordSzInBits() {
  // slice of metadata keys 2nd metadata key onwards
  auto sec_metadata_keys = hana::slice(
      hana::keys(m_submgrs),
      hana::make_range(hana::size_c<2>, TrackingMemoryTuple::GetTupleSize()));
  auto first_metadata_key = hana::keys(m_submgrs)[hana::size_c<1>];
  auto wordSz = hana::at_key(m_submgrs, first_metadata_key).wordSzInBits();
  // assert that all metadata has same word size
  BOOST_HANA_RUNTIME_ASSERT(hana::all_of(sec_metadata_keys, [&](auto key) {
    return hana::at_key(m_submgrs, key).wordSzInBits() == wordSz;
  }));
  return wordSz;
}
size_t TrackingRawMemManager::getNumOfMetadataSlots() {
  // first slot is main mem, so don't count that
  return TrackingMemoryTuple::GetTupleSize() - hana::size_c<1>;
}
Expr TrackingRawMemManager::isMetadataSet(MetadataKind kind, PtrTy p,
                                          MemValTy mem) {
  LOG("opsem", ERR << "isMetadataSet() not implemented!\n");
  return Expr();
}
TrackingRawMemManager::MemValTy TrackingRawMemManager::setMetadata(
    MetadataKind kind, TrackingRawMemManager::PtrTy p,
    TrackingRawMemManager::MemValTy mem, Expr val) {
  auto index = static_cast<size_t>(kind) + 1;
  auto r =
      hana::make_range(hana::int_c<0>, TrackingMemoryTuple::GetTupleSize());
  auto r_t = hana::to_tuple(r);
  auto z_t = hana::zip(r_t, hana::keys(m_submgrs));
  auto c = hana::transform(z_t, [&](auto pair) {
    auto current = hana::at(pair, hana::size_c<0>);
    auto key = hana::at(pair, hana::size_c<1>);
    if (current == index) {
      return hana::at_key(m_submgrs, key)
          .storeIntToMem(val, p, mem.getElementVal(index), g_MetadataByteWidth,
                         0);
    } else {
      return mem.getElementVal(current);
    }
  });
  return MemValTy(c);
}
Expr TrackingRawMemManager::ptrUlt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrUlt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSlt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrSlt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrUle(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrUle(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSle(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrSle(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrUgt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrUgt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSgt(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrSgt(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrUge(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrUge(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSge(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrSge(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrNe(TrackingRawMemManager::PtrTy p1,
                                  TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrNe(getAddressable(p1), getAddressable(p2));
}
Expr TrackingRawMemManager::ptrSub(TrackingRawMemManager::PtrTy p1,
                                   TrackingRawMemManager::PtrTy p2) const {
  return MAIN_MEM_MGR.ptrSub(getAddressable(p1), getAddressable(p2));
}
} // namespace details
} // namespace seahorn
