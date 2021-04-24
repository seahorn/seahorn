#include "BvOpSem2WideMemMgr.hh"
#include "BvOpSem2Allocators.hh"
#include "BvOpSem2Context.hh"
#include "BvOpSem2MemManagerMixin.hh"

#include "seahorn/Expr/ExprOpStruct.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {

static const unsigned int g_slotBitWidth = 64;
static const unsigned int g_slotByteWidth = g_slotBitWidth / 8;

static const unsigned int g_uninit_size = 0;
static const unsigned int g_num_slots = 2;

WideMemManager::WideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                               unsigned ptrSz, unsigned wordSz, bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_size(sem, ctx, ptrSz, g_slotByteWidth, useLambdas, true),
      m_uninit_size(m_ctx.alu().ui(g_uninit_size, g_slotBitWidth)),
      m_nullPtr(PtrTy(m_main.nullPtr(), m_uninit_size)) {}

Expr WideMemManager::castWordSzToSlotSz(const Expr val) const {
  if (wordSizeInBits() == g_slotBitWidth) {
    return val;
  } else if (g_slotBitWidth > wordSizeInBits()) {
    return m_ctx.alu().doSext(val, g_slotBitWidth, wordSizeInBits());
  } else {
    LOG("opsem", WARN << "widemem: Casting wordSz to slotSz - information may "
                         "be lost!\n");
    return m_ctx.alu().doTrunc(val, g_slotBitWidth);
  }
}
Expr WideMemManager::castPtrSzToSlotSz(const Expr val) const {
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
const OpSemMemManager &WideMemManager::getMainMemMgr() const { return m_main; }
Expr WideMemManager::getSize(WideMemManager::PtrTy p) { return p.getSize(); }
WideMemManager::RawPtrTy
WideMemManager::getAddressable(WideMemManager::PtrTy p) const {
  return p.getRaw();
}
Expr WideMemManager::isDereferenceable(WideMemManager::PtrTy p, Expr byteSz) {
  // size should be >= byteSz
  auto ptr_size = p.getSize();
  if (m_ctx.shouldSimplify()) {
    ptr_size = m_ctx.simplify(p.getSize());
    byteSz = m_ctx.simplify(byteSz);
  }
  if (m_ctx.alu().isNum(byteSz) && m_ctx.alu().isNum(ptr_size)) {
    signed numBytes = m_ctx.alu().toNum(byteSz).get_si();
    signed conc_size = m_ctx.alu().toNum(ptr_size).get_si();
    return conc_size >= numBytes ? m_ctx.alu().getTrue()
                                 : m_ctx.alu().getFalse();
  } else {
    return m_ctx.alu().doSge(ptr_size, castWordSzToSlotSz(byteSz),
                             g_slotBitWidth);
  }
}
WideMemManager::MemValTy WideMemManager::zeroedMemory() const {
  return MemValTy(m_main.zeroedMemory(), m_size.zeroedMemory());
}

std::pair<char *, unsigned int>
WideMemManager::getGlobalVariableInitValue(const GlobalVariable &gv) {
  return m_main.getGlobalVariableInitValue(gv);
}
void WideMemManager::dumpGlobalsMap() { m_main.dumpGlobalsMap(); }
void WideMemManager::onModuleEntry(const Module &M) { m_main.onModuleEntry(M); }
void WideMemManager::onFunctionEntry(const Function &fn) {
  m_main.onFunctionEntry(fn);
}
WideMemManager::PtrTy WideMemManager::gep(WideMemManager::PtrTy ptr,
                                          gep_type_iterator it,
                                          gep_type_iterator end) const {
  RawPtrTy rawPtr = m_main.gep(ptr.getRaw(), it, end);
  // offset bitwidth is ptrSz
  auto offset = m_main.ptrSub(rawPtr, ptr.getRaw());
  auto new_size = m_ctx.alu().doSub(ptr.getSize(), castPtrSzToSlotSz(offset),
                                    g_slotBitWidth);

  return PtrTy(rawPtr, new_size);
}
Expr WideMemManager::ptrEq(WideMemManager::PtrTy p1,
                           WideMemManager::PtrTy p2) const {
  return m_main.ptrEq(p1.getRaw(), p2.getRaw());
}
Expr WideMemManager::ptrtoint(WideMemManager::PtrTy ptr, const Type &ptrTy,
                              const Type &intTy) const {
  return m_main.ptrtoint(ptr.getRaw(), ptrTy, intTy);
}
WideMemManager::PtrTy WideMemManager::inttoptr(Expr intVal, const Type &intTy,
                                               const Type &ptrTy) const {
  return PtrTy(m_main.inttoptr(intVal, intTy, ptrTy), m_uninit_size);
}
WideMemManager::MemValTy WideMemManager::MemFill(WideMemManager::PtrTy dPtr,
                                                 char *sPtr, unsigned int len,
                                                 WideMemManager::MemValTy mem,
                                                 uint32_t align) {
  return MemValTy(m_main.MemFill(dPtr.getRaw(), sPtr, len, mem.getRaw(), align),
                  mem.getSize());
}
WideMemManager::MemValTy
WideMemManager::MemCpy(WideMemManager::PtrTy dPtr, WideMemManager::PtrTy sPtr,
                       Expr len, WideMemManager::MemValTy memTrsfrRead,
                       WideMemManager::MemValTy memRead, uint32_t align) {
  return MemValTy(m_main.MemCpy(dPtr.getRaw(), sPtr.getRaw(), len,
                                memTrsfrRead.getRaw(), memRead.getRaw(), align),
                  m_size.MemCpy(dPtr.getRaw(), sPtr.getRaw(), len,
                                memTrsfrRead.getSize(), memRead.getSize(),
                                align));
}
WideMemManager::MemValTy
WideMemManager::MemCpy(WideMemManager::PtrTy dPtr, WideMemManager::PtrTy sPtr,
                       unsigned int len, WideMemManager::MemValTy memTrsfrRead,
                       WideMemManager::MemValTy memRead, uint32_t align) {
  return MemValTy(m_main.MemCpy(dPtr.getRaw(), sPtr.getRaw(), len,
                                memTrsfrRead.getRaw(), memRead.getRaw(), align),
                  m_size.MemCpy(dPtr.getRaw(), sPtr.getRaw(), len,
                                memTrsfrRead.getSize(), memRead.getSize(),
                                align));
}
WideMemManager::MemValTy WideMemManager::MemSet(WideMemManager::PtrTy ptr,
                                                Expr _val, Expr len,
                                                WideMemManager::MemValTy mem,
                                                uint32_t align) {
  return MemValTy(m_main.MemSet(ptr.getRaw(), _val, len, mem.getRaw(), align),
                  mem.getSize());
}
WideMemManager::MemValTy WideMemManager::MemSet(WideMemManager::PtrTy ptr,
                                                Expr _val, unsigned int len,
                                                WideMemManager::MemValTy mem,
                                                uint32_t align) {
  return MemValTy(m_main.MemSet(ptr.getRaw(), _val, len, mem.getRaw(), align),
                  mem.getSize());
}
WideMemManager::MemValTy
WideMemManager::storeValueToMem(Expr _val, WideMemManager::PtrTy ptr,
                                WideMemManager::MemValTy memIn, const Type &ty,
                                uint32_t align) {
  assert(ptr.v());
  Expr val = _val;
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr.v()->efac();
  // init memval to a non det value
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
    res = storePtrToMem(PtrTy(val), ptr, memIn, byteSz, align);
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
Expr WideMemManager::loadValueFromMem(WideMemManager::PtrTy ptr,
                                      WideMemManager::MemValTy mem,
                                      const Type &ty, uint64_t align) {
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr.getRaw()->efac();

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
    res = loadPtrFromMem(ptr, mem, byteSz, align).v();
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
WideMemManager::MemValTy WideMemManager::storePtrToMem(
    WideMemManager::PtrTy val, WideMemManager::PtrTy ptr,
    WideMemManager::MemValTy mem, unsigned int byteSz, uint64_t align) {
  RawMemValTy main = m_main.storePtrToMem(val.getRaw(), ptr.getRaw(),
                                          mem.getRaw(), byteSz, align);
  RawMemValTy size = m_size.storeIntToMem(
      val.getSize(), ptr.getRaw(), mem.getSize(), g_slotByteWidth, align);
  return MemValTy(main, size);
}
WideMemManager::MemValTy
WideMemManager::storeIntToMem(Expr _val, WideMemManager::PtrTy ptr,
                              WideMemManager::MemValTy mem, unsigned int byteSz,
                              uint64_t align) {
  if (strct::isStructVal(_val)) {
    // LLVM can sometimes cast a ptr to int without ptrtoint
    // In such cases our VM will interpret the int rightly as a struct
    if (_val->arity() == g_num_slots) {
      LOG("opsem", WARN << "fixing: int is actually a struct, unpacking "
                           "before store\n");
      auto raw_val = strct::extractVal(_val, 0);
      auto size_val = strct::extractVal(_val, 1);
      return MemValTy(m_main.storeIntToMem(raw_val, ptr.getRaw(), mem.getRaw(),
                                           byteSz, align),
                      m_size.storeIntToMem(size_val, ptr.getRaw(),
                                           mem.getSize(), g_slotByteWidth,
                                           align));

    } else {
      LOG("opsem", ERR << "fixing: int is a struct: expected arity "
                       << g_num_slots << " but got " << _val->arity() << ".\n");
    }
  }
  return MemValTy(
      m_main.storeIntToMem(_val, ptr.getRaw(), mem.getRaw(), byteSz, align),
      mem.getSize());
}
WideMemManager::PtrTy
WideMemManager::loadPtrFromMem(WideMemManager::PtrTy ptr,
                               WideMemManager::MemValTy mem,
                               unsigned int byteSz, uint64_t align) {
  RawMemValTy rawVal =
      m_main.loadPtrFromMem(ptr.getRaw(), mem.getRaw(), byteSz, align);
  RawMemValTy sizeVal = m_size.loadIntFromMem(ptr.getRaw(), mem.getSize(),
                                              g_slotByteWidth, align);
  return PtrTy(rawVal, sizeVal);
}
Expr WideMemManager::loadIntFromMem(WideMemManager::PtrTy ptr,
                                    WideMemManager::MemValTy mem,
                                    unsigned int byteSz, uint64_t align) {
  return m_main.loadIntFromMem(ptr.getRaw(), mem.getRaw(), byteSz, align);
}
WideMemManager::PtrTy WideMemManager::ptrAdd(WideMemManager::PtrTy ptr,
                                             Expr offset) const {
  if (m_ctx.alu().isNum(offset)) {
    expr::mpz_class _offset = m_ctx.alu().toNum(offset);
    return ptrAdd(ptr, _offset.get_si());
  }
  // TODO: What is the bitwidth of offset here?
  auto address = m_ctx.alu().doAdd(ptr.getRaw(), offset, ptrSizeInBits());
  auto new_size = m_ctx.alu().doSub(ptr.getSize(), offset, g_slotBitWidth);

  return PtrTy(address, new_size);
}
WideMemManager::PtrTy WideMemManager::ptrAdd(WideMemManager::PtrTy ptr,
                                             int32_t offset) const {
  if (offset == 0)
    return ptr;
  auto address = m_ctx.alu().doAdd(
      ptr.getRaw(), m_ctx.alu().si(offset, ptrSizeInBits()), ptrSizeInBits());
  Expr new_size;
  // do concrete computation if possible.
  if (m_ctx.alu().isNum(ptr.getSize())) {
    signed conc_size = m_ctx.alu().toNum(ptr.getSize()).get_si();
    new_size = m_ctx.alu().si(conc_size - offset, g_slotBitWidth);
  } else {
    new_size = m_ctx.alu().doSub(
        ptr.getSize(), m_ctx.alu().si(offset, g_slotBitWidth), g_slotBitWidth);
  }
  return PtrTy(address, new_size);
}
Expr WideMemManager::coerce(Expr sort, Expr val) {
  if (strct::isStructVal(val)) {
    // recursively coerce struct-ty
    llvm::SmallVector<Expr, 8> kids;
    assert(isOp<STRUCT_TY>(sort));
    assert(sort->arity() == val->arity());
    for (unsigned i = 0, sz = val->arity(); i < sz; ++i)
      kids.push_back(coerce(sort->arg(i), val->arg(i)));
    return strct::mk(kids);
  }

  return m_main.coerce(sort, val);
}
WideMemManager::PtrTy WideMemManager::freshPtr() {
  Expr name = op::variant::variant(m_id++, m_freshPtrName);
  return mkAlignedPtr(name, m_alignment);
}
WideMemManager::MemSortTy
WideMemManager::mkMemRegisterSort(const Instruction &inst) const {
  RawMemSortTy mainSort = m_main.mkMemRegisterSort(inst);
  RawMemSortTy sizeSort = m_size.mkMemRegisterSort(inst);
  return MemSortTy(mainSort, sizeSort);
}
WideMemManager::PtrSortTy
WideMemManager::mkPtrRegisterSort(const GlobalVariable &gv) const {
  return ptrSort();
}
WideMemManager::PtrSortTy
WideMemManager::mkPtrRegisterSort(const Function &fn) const {
  return ptrSort();
}
WideMemManager::PtrSortTy
WideMemManager::mkPtrRegisterSort(const Instruction &inst) const {
  return PtrSortTy(m_main.mkPtrRegisterSort(inst),
                   m_ctx.alu().intTy(g_slotBitWidth));
}
WideMemManager::PtrTy WideMemManager::mkAlignedPtr(Expr name,
                                                   uint32_t align) const {
  m_size.mkAlignedPtr(name, align);
  return PtrTy(m_main.mkAlignedPtr(name, align), m_uninit_size);
}
void WideMemManager::initGlobalVariable(const GlobalVariable &gv) const {
  m_main.initGlobalVariable(gv);
}
WideMemManager::PtrTy
WideMemManager::getPtrToGlobalVariable(const GlobalVariable &gv) {
  // TODO: Add a map of ptr to AllocInfo in allocator so that given any ptr,
  // we can get size of allocation.
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  return PtrTy(m_ctx.alu().ui(m_main.getMAllocator().getGlobalVariableAddr(
                                  gv, gvSz, m_alignment),
                              ptrSizeInBits()),
               bytesToSlotExpr(gvSz));
}
WideMemManager::PtrTy WideMemManager::getPtrToFunction(const Function &F) {
  auto rawPtr = m_ctx.alu().ui(
      m_main.getMAllocator().getFunctionAddrAndSize(F, m_alignment).first,
      ptrSizeInBits());
  auto size = m_ctx.alu().ui(
      m_main.getMAllocator().getFunctionAddrAndSize(F, m_alignment).second,
      g_slotBitWidth);
  return PtrTy(rawPtr, size);
}
WideMemManager::PtrTy WideMemManager::falloc(const Function &fn) {
  auto range = m_main.getMAllocator().falloc(fn, m_alignment);
  return PtrTy(m_ctx.alu().ui(range.first, ptrSizeInBits()),
               bytesToSlotExpr(range.second - range.first));
}
WideMemManager::PtrTy WideMemManager::galloc(const GlobalVariable &gv,
                                             uint32_t align) {
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  auto range =
      m_main.getMAllocator().galloc(gv, gvSz, std::max(align, m_alignment));
  return PtrTy(m_ctx.alu().ui(range.first, ptrSizeInBits()),
               bytesToSlotExpr(range.second - range.first));
}
WideMemManager::PtrTy WideMemManager::halloc(Expr bytes, uint32_t align) {
  PtrTy res = freshPtr();
  LOG("opsem", WARN << "halloc() not implemented!\n");
  return res;
}
WideMemManager::PtrTy WideMemManager::halloc(unsigned int _bytes,
                                             uint32_t align) {
  PtrTy res = freshPtr();
  LOG("opsem", WARN << "halloc() not implemented!\n");
  return res;
}
WideMemManager::PtrTy WideMemManager::brk0Ptr() {
  return PtrTy(m_main.brk0Ptr(), m_uninit_size);
}
WideMemManager::PtrTy WideMemManager::mkStackPtr(unsigned int offset) {
  return PtrTy(m_main.mkStackPtr(offset), m_uninit_size);
}
WideMemManager::PtrTy WideMemManager::salloc(Expr elmts, unsigned int typeSz,
                                             uint32_t align) {
  align = std::max(align, m_alignment);

  // -- compute number of bytes needed
  Expr bytes = elmts;
  if (typeSz > 1) {
    // TODO: factor out multiplication and number creation
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
  return PtrTy(mkStackPtr(region.second).getRaw(),
               m_ctx.alu().ui(region.first - region.second, g_slotBitWidth));
}
WideMemManager::PtrTy WideMemManager::salloc(unsigned int bytes,
                                             uint32_t align) {
  assert(isa<AllocaInst>(m_ctx.getCurrentInst()));
  align = std::max(align, m_alignment);
  auto region = m_main.getMAllocator().salloc(bytes, align);
  assert(region.second > region.first);
  // The size is min(alloc_size, requested_size)
  return PtrTy(mkStackPtr(region.second).getRaw(),
               bytesToSlotExpr(std::min(region.second - region.first, bytes)));
}
WideMemManager::PtrSortTy WideMemManager::ptrSort() const {
  return PtrSortTy(m_main.ptrSort(), m_ctx.alu().intTy(g_slotBitWidth));
}
Expr WideMemManager::bytesToSlotExpr(unsigned int bytes) {
  return m_ctx.alu().ui(bytes, g_slotBitWidth);
}
Expr WideMemManager::ptrUlt(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrUlt(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrSlt(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrSlt(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrUle(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrUle(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrSle(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrSle(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrUgt(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrUgt(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrSgt(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrSgt(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrUge(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrUge(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrSge(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrSge(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrNe(WideMemManager::PtrTy p1,
                           WideMemManager::PtrTy p2) const {
  return m_main.ptrNe(getAddressable(p1), getAddressable(p2));
}
Expr WideMemManager::ptrSub(WideMemManager::PtrTy p1,
                            WideMemManager::PtrTy p2) const {
  return m_main.ptrSub(getAddressable(p1), getAddressable(p2));
}

bool WideMemManager::isPtrTyVal(Expr e) const {
  return e && strct::isStructVal(e) && e->arity() == g_num_slots;
}

bool WideMemManager::isMemVal(Expr e) const {
  // struct of raw and size
  return e && strct::isStructVal(e) && e->arity() == g_num_slots;
}

OpSemMemManager *mkWideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                  unsigned ptrSz, unsigned wordSz,
                                  bool useLambdas) {
  return new OpSemMemManagerMixin<WideMemManager>(sem, ctx, ptrSz, wordSz,
                                                  useLambdas);
}
} // namespace details
} // namespace seahorn
