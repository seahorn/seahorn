#include "BvOpSem2ExtraWideMemMgr.hh"
#include "BvOpSem2Allocators.hh"
#include "BvOpSem2Context.hh"
#include "BvOpSem2MemManagerMixin.hh"

#include <boost/hana.hpp>
#include <type_traits>

namespace seahorn {
namespace details {

static const unsigned int g_slotBitWidth = 64;
static const unsigned int g_slotByteWidth = g_slotBitWidth / 8;

static const unsigned int g_uninit = 0xDEADBEEF;
static const unsigned int g_uninit_small = 0xDEAD;
static const unsigned int g_num_slots = 3;

template <class T>
ExtraWideMemManager<T>::ExtraWideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                            unsigned ptrSz, unsigned wordSz,
                                            bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_offset(sem, ctx, ptrSz, ptrSz, useLambdas, true),
      m_size(sem, ctx, ptrSz, g_slotByteWidth, useLambdas, true),
      m_uninit_size(m_ctx.alu().ui(g_uninit, g_slotBitWidth)),
      m_nullPtr(PtrTy(m_main.nullPtr(), m_ctx.alu().ui(0UL, ptrSizeInBits()),
                      m_uninit_size)) {
  // Currently, we only support RawMemManagerCore or subclasses of it.
  static_assert(std::is_base_of<OpSemMemManagerBase, T>::value,
                "T not derived from OpSemMemManagerBase");
  LOG("opsem", INFO << hana::eval_if(
                   MemoryFeatures::has_tracking(hana::type<T>{}),
                   [&] { return "Memory tracking on"; },
                   [&] { return "Memory tracking off"; }));
}

template <class T>
typename ExtraWideMemManager<T>::RawMemValTy
ExtraWideMemManager<T>::setModified(ExtraWideMemManager::PtrTy ptr,
                                    ExtraWideMemManager::MemValTy mem) {
  return memsetMetaData(ptr, 1 /* len */, mem, 1U /* val */).getRaw();
}

template <class T>
Expr ExtraWideMemManager<T>::isModified(ExtraWideMemManager::PtrTy ptr,
                                        ExtraWideMemManager::MemValTy mem) {
  // The width of the value will be wordSz
  Expr val = getMetaData(ptr, mem, 1);
  if (val == Expr()) {
    return m_ctx.alu().getTrue();
  }
  auto sentinel = m_ctx.alu().ui(1, getMetaDataMemWordSzInBits());
  return m_ctx.alu().doEq(val, sentinel, getMetaDataMemWordSzInBits());
}
template <class T>
Expr ExtraWideMemManager<T>::ptrEq(ExtraWideMemManager::PtrTy p1,
                                   ExtraWideMemManager::PtrTy p2) const {
  return mk<AND>(m_main.ptrEq(p1.getBase(), p2.getBase()),
                 m_offset.ptrEq(p1.getOffset(), p2.getOffset()));
}
template <class T>
Expr ExtraWideMemManager<T>::castPtrSzToSlotSz(const Expr val) const {
  if (ptrSizeInBits() == g_slotBitWidth) {
    return val;
  } else if (g_slotBitWidth > ptrSizeInBits()) {
    return m_ctx.alu().doSext(val, g_slotBitWidth, ptrSizeInBits());
  } else {
    LOG("opsem", WARN << "widemem: Casting ptrSz to slotSz - information may "
                         "be lost!\n");
    return m_ctx.alu().doTrunc(val, g_slotBitWidth);
  }
}
template <class T>
const OpSemMemManager &ExtraWideMemManager<T>::getMainMemMgr() const {
  return m_main;
}
template <class T>
Expr ExtraWideMemManager<T>::getSize(ExtraWideMemManager::PtrTy p) const {
  return p.getSize();
}
template <class T>
typename ExtraWideMemManager<T>::RawPtrTy
ExtraWideMemManager<T>::getAddressable(ExtraWideMemManager::PtrTy p) const {
  // do concrete computation if possible
  // NOTE: This is needed in ConstantEvaluator
  // TODO: This computation will be incorrect if base ptr type is not a raw expr
  // Alternative is for each mem mgr to have a getAddressable and to delegate
  // to that manager rather than assuming a raw expr.
  if (m_ctx.alu().isNum(p.getBase()) && m_ctx.alu().isNum(p.getOffset())) {
    // -- base pointer is unsigned, but offset can be negative
    unsigned ptrBase = m_ctx.alu().toNum(p.getBase()).get_ui();
    signed offset = m_ctx.alu().toNum(p.getOffset()).get_si();
    return m_ctx.alu().ui(ptrBase + offset, ptrSizeInBits());
  }
  return m_ctx.alu().doAdd(p.getBase(), p.getOffset(), ptrSizeInBits());
}
template <class T>
Expr ExtraWideMemManager<T>::isDereferenceable(ExtraWideMemManager::PtrTy p,
                                               Expr byteSz) {
  // size should be >= byteSz + offset
  auto ptr_size = p.getSize();
  auto ptr_offset = p.getOffset();

  if (m_ctx.shouldSimplify()) {
    ptr_size = m_ctx.simplify(p.getSize());
    ptr_offset = m_ctx.simplify(p.getOffset());
    byteSz = m_ctx.simplify(byteSz);
  }
  if (m_ctx.alu().isNum(byteSz) && m_ctx.alu().isNum(ptr_size) &&
      m_ctx.alu().isNum(ptr_offset)) {
    signed numBytes = m_ctx.alu().toNum(byteSz).get_si();
    signed conc_size = m_ctx.alu().toNum(ptr_size).get_si();
    signed conc_offset = m_ctx.alu().toNum(ptr_offset).get_si();
    return conc_size >= numBytes + conc_offset ? m_ctx.alu().getTrue()
                                               : m_ctx.alu().getFalse();
  } else {
    auto lastBytePos = m_ctx.alu().doAdd(byteSz, ptr_offset, ptrSizeInBits());
    return m_ctx.alu().doSge(ptr_size, castPtrSzToSlotSz(lastBytePos),
                             g_slotBitWidth);
  }
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy
ExtraWideMemManager<T>::zeroedMemory() const {
  return MemValTy(m_main.zeroedMemory(), m_offset.zeroedMemory(),
                  m_size.zeroedMemory());
}
template <class T>
std::pair<char *, unsigned int>
ExtraWideMemManager<T>::getGlobalVariableInitValue(const GlobalVariable &gv) {
  return m_main.getGlobalVariableInitValue(gv);
}
template <class T> void ExtraWideMemManager<T>::dumpGlobalsMap() {
  m_main.dumpGlobalsMap();
}
template <class T> void ExtraWideMemManager<T>::onModuleEntry(const Module &M) {
  m_main.onModuleEntry(M);
}
template <class T>
void ExtraWideMemManager<T>::onFunctionEntry(const Function &fn) {
  m_main.onFunctionEntry(fn);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::gep(ExtraWideMemManager::PtrTy base,
                            gep_type_iterator it, gep_type_iterator end) const {
  // offset bitwidth is ptrSz
  Expr new_offset = m_sem.symbolicIndexedOffset(it, end, m_ctx);
  return PtrTy(base.getBase(),
               m_ctx.alu().doAdd(base.getOffset(), new_offset, ptrSizeInBits()),
               base.getSize());
}
template <class T>
Expr ExtraWideMemManager<T>::ptrtoint(ExtraWideMemManager::PtrTy base,
                                      const Type &ptrTy,
                                      const Type &intTy) const {
  return m_main.ptrtoint(getAddressable(base), ptrTy, intTy);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::inttoptr(Expr intVal, const Type &intTy,
                                 const Type &ptrTy) const {
  return PtrTy(m_main.inttoptr(intVal, intTy, ptrTy),
               m_ctx.alu().ui(0UL, ptrSizeInBits()), m_uninit_size);
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy ExtraWideMemManager<T>::MemFill(
    ExtraWideMemManager::PtrTy dPtr, char *sPtr, unsigned int len,
    ExtraWideMemManager::MemValTy mem, uint32_t align) {
  RawMemValTy rawIn = setModified(dPtr, mem);
  return MemValTy(m_main.MemFill(getAddressable(dPtr), sPtr, len, rawIn, align),
                  mem.getOffset(), mem.getSize());
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy ExtraWideMemManager<T>::MemCpy(
    ExtraWideMemManager::PtrTy dPtr, ExtraWideMemManager::PtrTy sPtr, Expr len,
    ExtraWideMemManager::MemValTy memTrsfrRead,
    ExtraWideMemManager::MemValTy memRead, uint32_t align) {
  // set metadata of dest memory
  RawMemValTy rawIn = setModified(dPtr, memRead);
  return MemValTy(
      m_main.MemCpy(getAddressable(dPtr), getAddressable(sPtr), len,
                    memTrsfrRead.getRaw(), rawIn, align),
      m_offset.MemCpy(getAddressable(dPtr), getAddressable(sPtr), len,
                      memTrsfrRead.getOffset(), memRead.getOffset(), align),
      m_size.MemCpy(getAddressable(dPtr), getAddressable(sPtr), len,
                    memTrsfrRead.getSize(), memRead.getSize(), align));
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy ExtraWideMemManager<T>::MemCpy(
    ExtraWideMemManager::PtrTy dPtr, ExtraWideMemManager::PtrTy sPtr,
    unsigned int len, ExtraWideMemManager::MemValTy memTrsfrRead,
    ExtraWideMemManager::MemValTy memRead, uint32_t align) {
  // set metadata of dest memory
  RawMemValTy rawIn = setModified(dPtr, memRead);
  return MemValTy(
      m_main.MemCpy(getAddressable(dPtr), getAddressable(sPtr), len,
                    memTrsfrRead.getRaw(), rawIn, align),
      m_offset.MemCpy(getAddressable(dPtr), getAddressable(sPtr), len,
                      memTrsfrRead.getOffset(), memRead.getOffset(), align),
      m_size.MemCpy(getAddressable(dPtr), getAddressable(sPtr), len,
                    memTrsfrRead.getSize(), memRead.getSize(), align));
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy
ExtraWideMemManager<T>::MemSet(ExtraWideMemManager::PtrTy base, Expr _val,
                               Expr len, ExtraWideMemManager::MemValTy mem,
                               uint32_t align) {
  Expr offsetMem = mem.getOffset();
  if (m_ctx.alu().isNum(_val) && m_ctx.alu().toNum(_val) == 0) {
    offsetMem =
        m_offset.MemSet(getAddressable(base), _val, len, offsetMem, align);
  }
  RawMemValTy rawIn = setModified(base, mem);
  return MemValTy(m_main.MemSet(getAddressable(base), _val, len, rawIn, align),
                  offsetMem, mem.getSize());
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy ExtraWideMemManager<T>::MemSet(
    ExtraWideMemManager::PtrTy base, Expr _val, unsigned int len,
    ExtraWideMemManager::MemValTy mem, uint32_t align) {
  Expr offsetMem = mem.getOffset();

  // -- memset(0) is a common idiom to override everything, including
  // pointers, with 0
  // -- Thus, we must clear an offset field as well
  if (m_ctx.alu().isNum(_val) && m_ctx.alu().toNum(_val) == 0) {
    offsetMem =
        m_offset.MemSet(getAddressable(base), _val, len, offsetMem, align);
  }
  RawMemValTy rawIn = setModified(base, mem);
  return MemValTy(m_main.MemSet(getAddressable(base), _val, len, rawIn, align),
                  offsetMem, mem.getSize());
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy
ExtraWideMemManager<T>::storeValueToMem(Expr _val,
                                        ExtraWideMemManager::PtrTy base,
                                        ExtraWideMemManager::MemValTy memIn,
                                        const Type &ty, uint32_t align) {
  assert(base.v());
  Expr val = _val;
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = base.v()->efac();
  // init memval to a default value
  MemValTy res(m_main.zeroedMemory(),
               m_ctx.alu().ui(g_uninit_small, wordSizeInBits()), m_uninit_size);
  switch (ty.getTypeID()) {
  case Type::IntegerTyID:
    if (ty.getScalarSizeInBits() < byteSz * 8) {
      val = m_ctx.alu().doZext(val, byteSz * 8, ty.getScalarSizeInBits());
    }
    res = storeIntToMem(val, base, memIn, byteSz, align);
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
    res = storePtrToMem(PtrTy(val), base, memIn, byteSz, align);
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
Expr ExtraWideMemManager<T>::loadValueFromMem(ExtraWideMemManager::PtrTy base,
                                              ExtraWideMemManager::MemValTy mem,
                                              const Type &ty, uint64_t align) {
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = base.getBase()->efac();

  Expr res;
  switch (ty.getTypeID()) {
  case Type::IntegerTyID:
    res = loadIntFromMem(base, mem, byteSz, align);
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
    res = loadPtrFromMem(base, mem, byteSz, align).v();
    break;
  case Type::StructTyID:
    errs() << "loading form struct type " << ty << " is not supported";
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
typename ExtraWideMemManager<T>::MemValTy ExtraWideMemManager<T>::storePtrToMem(
    ExtraWideMemManager::PtrTy val, ExtraWideMemManager::PtrTy base,
    ExtraWideMemManager::MemValTy mem, unsigned int byteSz, uint64_t align) {
  RawMemValTy rawIn = setModified(base, mem);
  RawMemValTy main = m_main.storePtrToMem(val.getBase(), getAddressable(base),
                                          rawIn, byteSz, align);
  Expr offset = m_offset.storeIntToMem(val.getOffset(), getAddressable(base),
                                       mem.getOffset(), byteSz, align);
  Expr size = m_size.storeIntToMem(val.getSize(), getAddressable(base),
                                   mem.getSize(), g_slotByteWidth, align);
  return MemValTy(main, offset, size);
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy ExtraWideMemManager<T>::storeIntToMem(
    Expr _val, ExtraWideMemManager::PtrTy base,
    ExtraWideMemManager::MemValTy mem, unsigned int byteSz, uint64_t align) {
  if (strct::isStructVal(_val)) {
    // LLVM can sometimes cast a ptr to int without ptrtoint
    // In such cases our VM will interpret the int rightly as a struct
    if (_val->arity() == g_num_slots) {
      LOG("opsem", WARN << "fixing: int is actually a struct, unpacking "
                           "before store\n");
      auto base_val = strct::extractVal(_val, 0);
      auto offset_val = strct::extractVal(_val, 1);
      auto size_val = strct::extractVal(_val, 2);
      RawMemValTy rawIn = setModified(base, mem);
      return MemValTy(m_main.storeIntToMem(base_val, getAddressable(base),
                                           rawIn, byteSz, align),
                      m_offset.storeIntToMem(offset_val, getAddressable(base),
                                             mem.getOffset(), byteSz, align),
                      m_size.storeIntToMem(size_val, getAddressable(base),
                                           mem.getSize(), g_slotByteWidth,
                                           align));
    } else {

      LOG("opsem", ERR << "fixing: int is a struct: expected arity "
                       << g_num_slots << " but got " << _val->arity() << ".\n");
    }
  }
  RawMemValTy rawIn = setModified(base, mem);
  return MemValTy(
      m_main.storeIntToMem(_val, getAddressable(base), rawIn, byteSz, align),
      mem.getOffset(), mem.getSize());
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::loadPtrFromMem(ExtraWideMemManager::PtrTy base,
                                       ExtraWideMemManager::MemValTy mem,
                                       unsigned int byteSz, uint64_t align) {
  RawPtrTy rawVal =
      m_main.loadPtrFromMem(getAddressable(base), mem.getRaw(), byteSz, align);
  Expr offsetVal = m_offset.loadIntFromMem(getAddressable(base),
                                           mem.getOffset(), byteSz, align);
  Expr sizeVal = m_size.loadIntFromMem(getAddressable(base), mem.getSize(),
                                       g_slotByteWidth, align);
  return PtrTy(rawVal, offsetVal, sizeVal);
}
template <class T>
Expr ExtraWideMemManager<T>::loadIntFromMem(ExtraWideMemManager::PtrTy base,
                                            ExtraWideMemManager::MemValTy mem,
                                            unsigned int byteSz,
                                            uint64_t align) {
  return m_main.loadIntFromMem(getAddressable(base), mem.getRaw(), byteSz,
                               align);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::ptrAdd(ExtraWideMemManager::PtrTy base,
                               Expr offset) const {
  if (m_ctx.alu().isNum(offset)) {
    expr::mpz_class _offset = m_ctx.alu().toNum(offset);
    return ptrAdd(base, _offset.get_si());
  }
  // TODO: What is the bitwidth of offset here?
  auto new_offset =
      m_ctx.alu().doAdd(base.getOffset(), offset, ptrSizeInBits());

  return PtrTy(base.getBase(), new_offset, base.getSize());
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::ptrAdd(ExtraWideMemManager::PtrTy base,
                               int32_t _offset) const {
  // add offset to existing offset
  // base, size remain unchanged
  if (_offset == 0)
    return base;
  Expr new_offset;
  // do concrete computation if possible
  if (m_ctx.alu().isNum(base.getOffset())) {
    signed conc_offset = m_ctx.alu().toNum(base.getOffset()).get_si() + _offset;
    new_offset = m_ctx.alu().si(conc_offset, ptrSizeInBits());
  } else {
    auto new_offset = m_ctx.alu().doAdd(
        base.getOffset(), m_ctx.alu().si(_offset, ptrSizeInBits()),
        ptrSizeInBits());
  }
  return PtrTy(base.getBase(), new_offset, base.getSize());
}
template <class T> Expr ExtraWideMemManager<T>::coerce(Expr sort, Expr val) {
  if (strct::isStructVal(val)) {
    // recursively coerce struct-ty
    llvm::SmallVector<Expr, g_num_slots> kids;
    assert(isOp<STRUCT_TY>(sort));
    assert(sort->arity() == val->arity());
    assert(sort->arity() == g_num_slots);
    kids.push_back(m_main.coerce(sort->arg(0), val->arg(0)));
    kids.push_back(m_offset.coerce(sort->arg(1), val->arg(1)));
    kids.push_back(m_size.coerce(sort->arg(2), val->arg(2)));
    return strct::mk(kids);
  }
  return m_main.coerce(sort, val);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy ExtraWideMemManager<T>::nullPtr() const {
  return m_nullPtr;
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy ExtraWideMemManager<T>::freshPtr() {
  Expr name = op::variant::variant(m_id++, m_freshPtrName);
  return mkAlignedPtr(name, m_alignment);
}
template <class T>
typename ExtraWideMemManager<T>::MemSortTy
ExtraWideMemManager<T>::mkMemRegisterSort(const Instruction &inst) const {
  RawMemSortTy mainSort = m_main.mkMemRegisterSort(inst);
  RawMemSortTy offsetSort = m_offset.mkMemRegisterSort(inst);
  RawMemSortTy sizeSort = m_size.mkMemRegisterSort(inst);
  return MemSortTy(mainSort, offsetSort, sizeSort);
}
template <class T>
typename ExtraWideMemManager<T>::PtrSortTy
ExtraWideMemManager<T>::mkPtrRegisterSort(const Function &fn) const {
  return ptrSort();
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::mkAlignedPtr(Expr name, uint32_t align) const {
  m_size.mkAlignedPtr(name, align);
  return PtrTy(m_main.mkAlignedPtr(name, align),
               m_ctx.alu().ui(0UL, ptrSizeInBits()), m_uninit_size);
}
template <class T>
typename ExtraWideMemManager<T>::PtrSortTy
ExtraWideMemManager<T>::mkPtrRegisterSort(const Instruction &inst) const {
  return PtrSortTy(m_main.mkPtrRegisterSort(inst),
                   m_offset.mkPtrRegisterSort(inst),
                   m_ctx.alu().intTy(g_slotBitWidth));
}
template <class T>
typename ExtraWideMemManager<T>::PtrSortTy
ExtraWideMemManager<T>::mkPtrRegisterSort(const GlobalVariable &gv) const {
  return ptrSort();
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::getPtrToGlobalVariable(const GlobalVariable &gv) {
  // TODO: Add a map of base to AllocInfo in allocator so that given any base,
  // we can get size of allocation.
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  return PtrTy(m_ctx.alu().ui(m_main.getMAllocator().getGlobalVariableAddr(
                                  gv, gvSz, m_alignment),
                              ptrSizeInBits()),
               m_ctx.alu().ui(0UL, ptrSizeInBits()), bytesToSlotExpr(gvSz));
}
template <class T>
void ExtraWideMemManager<T>::initGlobalVariable(
    const GlobalVariable &gv) const {
  m_main.initGlobalVariable(gv);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::getPtrToFunction(const Function &F) {
  auto rawPtr = m_ctx.alu().ui(
      m_main.getMAllocator().getFunctionAddrAndSize(F, m_alignment).first,
      ptrSizeInBits());
  auto size = m_ctx.alu().ui(
      m_main.getMAllocator().getFunctionAddrAndSize(F, m_alignment).second,
      g_slotBitWidth);
  return PtrTy(rawPtr, m_ctx.alu().ui(0UL, ptrSizeInBits()), size);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::falloc(const Function &fn) {
  auto range = m_main.getMAllocator().falloc(fn, m_alignment);
  return PtrTy(m_ctx.alu().ui(range.first, ptrSizeInBits()),
               m_ctx.alu().ui(0UL, ptrSizeInBits()),
               bytesToSlotExpr(range.second - range.first));
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::galloc(const GlobalVariable &gv, uint32_t align) {
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  auto range =
      m_main.getMAllocator().galloc(gv, gvSz, std::max(align, m_alignment));
  return PtrTy(m_ctx.alu().ui(range.first, ptrSizeInBits()),
               m_ctx.alu().ui(0UL, ptrSizeInBits()),
               bytesToSlotExpr(range.second - range.first));
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::halloc(Expr bytes, uint32_t align) {
  PtrTy res = freshPtr();
  LOG("opsem", WARN << "halloc() not implemented!\n");
  return res;
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::halloc(unsigned int _bytes, uint32_t align) {
  PtrTy res = freshPtr();
  LOG("opsem", WARN << "halloc() not implemented!\n");
  return res;
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy ExtraWideMemManager<T>::brk0Ptr() {
  return PtrTy(m_main.brk0Ptr(), m_ctx.alu().ui(0UL, ptrSizeInBits()),
               m_uninit_size);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::mkStackPtr(unsigned int offset) {
  return PtrTy(m_main.mkStackPtr(offset), m_ctx.alu().ui(0UL, ptrSizeInBits()),
               m_uninit_size);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::salloc(Expr elmts, unsigned int typeSz,
                               uint32_t align) {
  align = std::max(align, m_alignment);

  // -- compute number of bytes needed
  Expr bytes = elmts;
  if (typeSz > 1) {
    bytes = m_ctx.alu().doMul(bytes, m_ctx.alu().ui(typeSz, ptrSizeInBits()),
                              ptrSizeInBits());
  }

  // allocate
  auto region = m_main.getMAllocator().salloc(bytes, align);

  // -- if allocation failed, return some pointer
  if (m_main.getMAllocator().isBadAddrInterval(region)) {
    LOG("opsem", WARN << "imprecise handling of dynamically "
                      << "sized stack allocation of " << *elmts
                      << " elements of size" << typeSz << " bytes\n";);
    return freshPtr();
  }

  // -- have a good region, return pointer to it
  return PtrTy(mkStackPtr(region.second).getBase(),
               m_ctx.alu().ui(0UL, ptrSizeInBits()), bytes);
}
template <class T>
typename ExtraWideMemManager<T>::PtrTy
ExtraWideMemManager<T>::salloc(unsigned int bytes, uint32_t align) {
  assert(isa<AllocaInst>(m_ctx.getCurrentInst()));
  align = std::max(align, m_alignment);
  auto region = m_main.getMAllocator().salloc(bytes, align);
  assert(region.second > region.first);
  // The size is min(alloc_size, requested_size)
  return PtrTy(mkStackPtr(region.second).getBase(),
               m_ctx.alu().ui(0UL, ptrSizeInBits()),
               bytesToSlotExpr(std::min(region.second - region.first, bytes)));
}
template <class T>
typename ExtraWideMemManager<T>::PtrSortTy
ExtraWideMemManager<T>::ptrSort() const {
  return PtrSortTy(m_main.ptrSort(), m_offset.ptrSort(),
                   m_ctx.alu().intTy(g_slotBitWidth));
}
template <class T>
Expr ExtraWideMemManager<T>::bytesToSlotExpr(unsigned int bytes) {
  return m_ctx.alu().ui(bytes, g_slotBitWidth);
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy
ExtraWideMemManager<T>::memsetMetaData(ExtraWideMemManager::PtrTy ptr,
                                       unsigned int len,
                                       ExtraWideMemManager::MemValTy memIn,
                                       unsigned int val) {
  auto rawOut = m_main.memsetMetaData(ptr.getBase(), len, memIn.getRaw(), val);
  return MemValTy(rawOut, memIn.getOffset(), memIn.getSize());
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy
ExtraWideMemManager<T>::memsetMetaData(ExtraWideMemManager::PtrTy ptr, Expr len,
                                       ExtraWideMemManager::MemValTy memIn,
                                       unsigned int val) {
  auto rawOut = m_main.memsetMetaData(ptr.getBase(), len, memIn.getRaw(), val);
  return MemValTy(rawOut, memIn.getOffset(), memIn.getSize());
}

template <class T>
Expr ExtraWideMemManager<T>::getMetaData(ExtraWideMemManager::PtrTy ptr,
                                         ExtraWideMemManager::MemValTy memIn,
                                         unsigned int byteSz) {
  return m_main.getMetaData(ptr.getBase(), memIn.getRaw(), byteSz);
}

template <class T>
unsigned int ExtraWideMemManager<T>::getMetaDataMemWordSzInBits() {
  return m_main.getMetaDataMemWordSzInBits();
}
template <class T>
typename ExtraWideMemManager<T>::MemValTy
ExtraWideMemManager<T>::resetModified(ExtraWideMemManager::PtrTy ptr,
                                      ExtraWideMemManager::MemValTy mem) {
  return memsetMetaData(ptr, 1 /* len */, mem, 0U /* val */);
}
template <class T>
Expr ExtraWideMemManager<T>::ptrUlt(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrUlt(getAddressable(p1), getAddressable(p2));
}

template <class T>
Expr ExtraWideMemManager<T>::ptrSlt(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrSlt(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrUle(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrUle(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrSle(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrSle(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrUgt(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrUgt(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrSgt(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrSgt(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrUge(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrUge(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrSge(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrSge(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrNe(ExtraWideMemManager::PtrTy p1,
                                   ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrNe(getAddressable(p1), getAddressable(p2));
}
template <class T>
Expr ExtraWideMemManager<T>::ptrSub(ExtraWideMemManager::PtrTy p1,
                                    ExtraWideMemManager::PtrTy p2) const {
  return m_main.ptrSub(getAddressable(p1), getAddressable(p2));
}

OpSemMemManager *mkExtraWideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                       unsigned int ptrSz, unsigned int wordSz,
                                       bool useLambdas) {
  return new OpSemMemManagerMixin<ExtraWideMemManager<RawMemManager>>(
      sem, ctx, ptrSz, wordSz, useLambdas);
}
OpSemMemManager *mkTrackingExtraWideMemManager(Bv2OpSem &sem,
                                               Bv2OpSemContext &ctx,
                                               unsigned int ptrSz,
                                               unsigned int wordSz,
                                               bool useLambdas) {
  return new OpSemMemManagerMixin<
      ExtraWideMemManager<OpSemMemManagerMixin<TrackingRawMemManager>>>(
      sem, ctx, ptrSz, wordSz, useLambdas);
}

template class ExtraWideMemManager<RawMemManager>;
template class ExtraWideMemManager<OpSemMemManagerMixin<TrackingRawMemManager>>;

} // namespace details
} // namespace seahorn
