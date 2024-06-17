#include "BvOpSem2FatMemMgr.hh"
#include "BvOpSem2Context.hh"
#include "BvOpSem2ExtraWideMemMgr.hh"
#include "BvOpSem2MemManagerMixin.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpStruct.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include <boost/variant.hpp>

static llvm::cl::opt<unsigned> FatMemSlots(
    "horn-bv2-num-fat-slots",
    llvm::cl::desc("Number of fat slots to initiate FatMemManager with"),
    llvm::cl::init(3));

namespace seahorn {
namespace details {

template <class T> unsigned FatMemManagerCore<T>::g_FatMemSlots;

/// \brief Converts a raw ptr to fat ptr with default value for fat
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::mkFatPtr(MainPtrTy mainPtr) const {
  llvm::SmallVector<AnyPtrTy, 8> ptrVals;
  ptrVals.push_back(mainPtr);
  // assign fresh (nd) values to fat slots
  for (unsigned i = 0; i < g_FatMemSlots; i++) {
    llvm::SmallString<100> tempStorage;
    auto fullName = m_fatMemBaseName + "slot" + std::to_string(i);
    auto fullNameExpr =
        mkTerm<std::string>(fullName.toStringRef(tempStorage).str(), m_efac);
    Expr freshSlotVal = op::variant::variant(m_id, fullNameExpr);
    Expr slotBind =
        bind::mkConst(freshSlotVal, m_ctx.alu().intTy(g_slotBitWidth));
    m_id++;
    ptrVals.push_back(slotBind);
  }
  return PtrTy(ptrVals);
}

/// \brief Assembles a fat ptr from parts
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::mkFatPtr(llvm::SmallVector<AnyPtrTy, 8> slots) const {
  return PtrTy(slots);
}

/// \brief Update a given fat pointer with a "main" address value
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::updateFatPtr(MainPtrTy mainPtr, PtrTy fat) const {
  if (fat.v()->arity() == 1)
    return mkFatPtr(mainPtr);

  llvm::SmallVector<AnyPtrTy, 8> kids;
  assert(fat.v()->arity() == g_FatMemSlots + 1);
  kids.push_back(mainPtr);
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    kids.push_back(fat.v()->arg(i));
  }
  return PtrTy(strct::mk(kids));
}

/// \brief Extracts a "main" pointer out of a fat pointer
template <class T>
typename FatMemManagerCore<T>::MainPtrTy
FatMemManagerCore<T>::mkMainPtr(PtrTy fatPtr) const {
  assert(strct::isStructVal(fatPtr.v()));
  return fatPtr.getMain();
}

/// \brief Extracts a "main" memory value from a fat memory value
template <class T>
typename FatMemManagerCore<T>::MainMemValTy
FatMemManagerCore<T>::mkMainMem(MemValTy fatMem) const {
  assert(strct::isStructVal(fatMem.v()));
  return fatMem.getMain();
}

template <class T>
typename FatMemManagerCore<T>::RawMemValTy
FatMemManagerCore<T>::mkSlot0Mem(MemValTy fatMem) const {
  assert(strct::isStructVal(fatMem.v()));
  return fatMem.getSlot(1);
}

template <class T>
typename FatMemManagerCore<T>::RawMemValTy
FatMemManagerCore<T>::mkSlot1Mem(MemValTy fatMem) const {
  assert(strct::isStructVal(fatMem.v()));
  return fatMem.getSlot(2);
}

/// \brief Creates a fat memory value from raw memory with given values
/// for fat
template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::mkFatMem(llvm::SmallVector<AnyMemValTy, 8> vals) const {
  return MemValTy(vals);
}

template <class T>
typename FatMemManagerCore<T>::PtrSortTy FatMemManagerCore<T>::ptrSort() const {
  llvm::SmallVector<AnyPtrSortTy, 8> sorts;
  sorts.push_back(m_main.ptrSort());
  for (unsigned i = 0; i < g_FatMemSlots; i++) {
    sorts.push_back(m_ctx.alu().intTy(g_slotBitWidth));
  }
  return PtrSortTy(sorts);
}

/// \brief Allocates memory on the stack and returns a pointer to it
/// \param align is requested alignment. If 0, default alignment is used
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::salloc(unsigned bytes, uint32_t align) {
  auto e = m_main.salloc(bytes, align);
  return mkFatPtr(e);
}

/// \brief Allocates memory on the stack and returns a pointer to it
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::salloc(Expr elmts, unsigned typeSz, uint32_t align) {
  auto e = m_main.salloc(elmts, typeSz, align);
  return mkFatPtr(e);
}

/// \brief Returns a pointer value for a given stack allocation
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::mkStackPtr(unsigned offset) {
  return mkFatPtr(m_main.mkStackPtr(offset));
}

/// \brief Pointer to start of the heap
/// \brief Returns a pointer value for a given stack allocation
template <class T>
typename FatMemManagerCore<T>::PtrTy FatMemManagerCore<T>::brk0Ptr() {
  return mkFatPtr(m_main.brk0Ptr());
}

/// \brief Allocates memory on the heap and returns a pointer to it
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::halloc(unsigned _bytes, uint32_t align) {
  return mkFatPtr(m_main.halloc(_bytes, align));
}

/// \brief Allocates memory on the heap and returns pointer to it
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::halloc(Expr bytes, uint32_t align) {
  return mkFatPtr(m_main.halloc(bytes, align));
}

/// \brief Allocates memory in global (data/bss) segment for given global
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::galloc(const GlobalVariable &gv, uint32_t align) {
  for (auto memMgr : m_slots) {
    memMgr.galloc(gv, align);
  }
  return mkFatPtr(m_main.galloc(gv, align));
}

/// \brief Allocates memory in code segment for the code of a given
/// function
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::falloc(const Function &fn) {
  return mkFatPtr(m_main.falloc(fn));
}

/// \brief Returns a function pointer value for a given function
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::getPtrToFunction(const Function &F) {
  return mkFatPtr(m_main.getPtrToFunction(F));
}

/// \brief Returns a pointer to a global variable
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::getPtrToGlobalVariable(const GlobalVariable &gv) {
  return mkFatPtr(m_main.getPtrToGlobalVariable(gv));
}

/// \brief Initialize memory used by the global variable
template <class T>
void FatMemManagerCore<T>::initGlobalVariable(const GlobalVariable &gv) const {
  m_main.initGlobalVariable(gv);
}

/// \brief Creates a non-deterministic pointer that is aligned
///
/// Top bits of the pointer are named by \p name and last \c log2(align)
/// bits are set to zero
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::mkAlignedPtr(Expr name, uint32_t align) const {
  return mkFatPtr(m_main.mkAlignedPtr(name, align));
}

/// \brief Returns sort of a pointer register for an instruction
template <class T>
typename FatMemManagerCore<T>::PtrSortTy
FatMemManagerCore<T>::mkPtrRegisterSort(const Instruction &inst) const {
  llvm::SmallVector<AnyPtrSortTy, 8> sorts;
  sorts.push_back(m_main.mkPtrRegisterSort(inst));
  for (unsigned i = 0; i < g_FatMemSlots; i++) {
    sorts.push_back(m_ctx.alu().intTy(g_slotBitWidth));
  }
  return PtrSortTy(sorts);
}

/// \brief Returns sort of a pointer register for a function pointer
template <class T>
typename FatMemManagerCore<T>::PtrSortTy
FatMemManagerCore<T>::mkPtrRegisterSort(const Function &fn) const {
  return ptrSort();
}

/// \brief Returns sort of a pointer register for a global pointer
template <class T>
typename FatMemManagerCore<T>::PtrSortTy
FatMemManagerCore<T>::mkPtrRegisterSort(const GlobalVariable &gv) const {
  return ptrSort();
}

/// \brief Returns sort of memory-holding register for an instruction
template <class T>
typename FatMemManagerCore<T>::MemSortTy
FatMemManagerCore<T>::mkMemRegisterSort(const Instruction &inst) const {
  llvm::SmallVector<AnyMemSortTy, 8> sorts;
  sorts.push_back(m_main.mkMemRegisterSort(inst));
  for (auto memMgr : m_slots) {
    sorts.push_back(memMgr.mkMemRegisterSort(inst));
  }
  return MemSortTy(sorts);
}

/// \brief Returns a fresh aligned pointer value
template <class T>
typename FatMemManagerCore<T>::PtrTy FatMemManagerCore<T>::freshPtr() {
  return mkFatPtr(m_main.freshPtr());
}

/// \brief Returns a null ptr
template <class T>
typename FatMemManagerCore<T>::PtrTy FatMemManagerCore<T>::nullPtr() const {
  return mkFatPtr(m_main.nullPtr());
}

/// \brief Fixes the type of a havoced value to mach the representation
/// used by mem repr.
///
/// \param sort
/// \param val
/// \return the coerced value.
template <class T> Expr FatMemManagerCore<T>::coerce(Expr sort, Expr val) {
  if (strct::isStructVal(val)) {
    // recursively coerce struct-ty
    llvm::SmallVector<Expr, 8> kids;
    assert(isOp<STRUCT_TY>(sort));
    assert(sort->arity() == val->arity());
    assert(sort->arity() == 1 + g_FatMemSlots);
    kids.push_back(m_main.coerce(sort->arg(0), val->arg(0)));
    for (unsigned i = 1, sz = val->arity(); i < sz; ++i)
      kids.push_back(m_slots[i - 1].coerce(sort->arg(i), val->arg(i)));
    return strct::mk(kids);
  }

  return m_main.coerce(sort, val);
}

/// \brief Loads an integer of a given size from 'raw' memory register
///
/// \param[in] ptr pointer being accessed
/// \param[in] mem memory value into which \p ptr points
/// \param[in] byteSz size of the integer in bytes
/// \param[in] align known alignment of \p ptr
/// \return symbolic value of the read integer
template <class T>
Expr FatMemManagerCore<T>::loadIntFromMem(PtrTy ptr, MemValTy mem,
                                          unsigned byteSz, uint64_t align) {
  return m_main.loadIntFromMem(mkMainPtr(ptr), mkMainMem(mem), byteSz, align);
}

/// \brief Loads a pointer stored in memory
/// \sa loadIntFromMem
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                                     uint64_t align) {
  llvm::SmallVector<AnyPtrTy, 8> ptrVals;

  MainPtrTy rawVal =
      m_main.loadPtrFromMem(mkMainPtr(ptr), mkMainMem(mem), byteSz, align);
  ptrVals.push_back(rawVal);
  RawPtrTy rawPtr = getAddressable(ptr);
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    auto slotVal = m_slots[i - 1].loadIntFromMem(rawPtr, mem.getSlot(i),
                                                 g_slotByteWidth, align);
    ptrVals.push_back(slotVal);
  }
  return mkFatPtr(ptrVals);
}

/// \brief Pointer addition with numeric offset
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::ptrAdd(PtrTy ptr, int32_t _offset) const {
  MainPtrTy mainPtr = m_main.ptrAdd(mkMainPtr(ptr), _offset);
  return updateFatPtr(mainPtr, ptr);
}

/// \brief Pointer addition with symbolic offset
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::ptrAdd(PtrTy ptr, Expr offset) const {
  MainPtrTy mainPtr = m_main.ptrAdd(mkMainPtr(ptr), offset);
  return updateFatPtr(mainPtr, ptr);
}

/// \brief Stores an integer into memory
///
/// Returns an expression describing the state of memory in \c memReadReg
/// after the store
/// \sa loadIntFromMem
template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                                    unsigned byteSz, uint64_t align) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  assert(!strct::isStructVal(_val));
  memVals.push_back(m_main.storeIntToMem(_val, mkMainPtr(ptr), mkMainMem(mem),
                                         byteSz, align));
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(mem.getSlot(i));
  }
  return mkFatMem(memVals);
}

/// \brief Stores a pointer into memory
/// \sa storeIntToMem
template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                                    unsigned byteSz, uint64_t align) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;

  MainMemValTy main = m_main.storePtrToMem(mkMainPtr(val), mkMainPtr(ptr),
                                           mkMainMem(mem), byteSz, align);
  memVals.push_back(main);
  RawPtrTy rawPtr = getAddressable(ptr);
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    MainMemValTy slotVal = m_slots[i - 1].storeIntToMem(
        val.getSlot(i), rawPtr, mem.getSlot(i), g_slotByteWidth, align);
    memVals.push_back(slotVal);
  }
  return mkFatMem(memVals);
}

/// \brief Returns an expression corresponding to a load from memory
///
/// \param[in] ptr is the pointer being dereferenced
/// \param[in] memReg is the memory register being read
/// \param[in] ty is the type of value being loaded
/// \param[in] align is the known alignment of the load
template <class T>
Expr FatMemManagerCore<T>::loadValueFromMem(PtrTy ptr, MemValTy mem,
                                            const llvm::Type &ty,
                                            uint64_t align) {

  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  // ExprFactory &efac = ptr.v()->efac();

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
  case Type::FixedVectorTyID:
  case Type::ScalableVectorTyID:
    errs() << "Error: load of fixed vectors is not supported\n";
    llvm_unreachable(nullptr);
    break;
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

template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn,
                                      const llvm::Type &ty, uint32_t align) {
  assert(ptr.v());
  Expr val = _val;
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));

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
  case Type::FixedVectorTyID:
  case Type::ScalableVectorTyID:
    errs() << "Error: store of vectors is not supported\n";
    llvm_unreachable(nullptr);
    break;
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
    report_fatal_error(out.str());
  }
  return res;
}

/// \brief Executes symbolic memset with a concrete length
template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                             uint32_t align) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(
      m_main.MemSet(mkMainPtr(ptr), _val, len, mkMainMem(mem), align));
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(mem.getSlot(i));
  }
  return mkFatMem(memVals);
}

template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                             uint32_t align) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(
      m_main.MemSet(mkMainPtr(ptr), _val, len, mkMainMem(mem), align));
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(mem.getSlot(i));
  }
  return mkFatMem(memVals);
}

/// \brief Executes symbolic memcpy with concrete length
template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len,
                             MemValTy memTrsfrRead, MemValTy memRead,
                             uint32_t align) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(m_main.MemCpy(mkMainPtr(dPtr), mkMainPtr(sPtr), len,
                                  mkMainMem(memTrsfrRead), mkMainMem(memRead),
                                  align));
  RawPtrTy rawPtrDst = getAddressable(dPtr);
  RawPtrTy rawPtrSrc = getAddressable(sPtr);
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(m_slots[i - 1].MemCpy(rawPtrDst, rawPtrSrc, len,
                                            memTrsfrRead.getSlot(i),
                                            memRead.getSlot(i), align));
  }
  return mkFatMem(memVals);
}

/// \brief Executes symbolic memcpy with concrete length
template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len,
                             MemValTy memTrsfrRead, MemValTy memRead,
                             uint32_t align) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(m_main.MemCpy(mkMainPtr(dPtr), mkMainPtr(sPtr), len,
                                  mkMainMem(memTrsfrRead), mkMainMem(memRead),
                                  align));
  RawPtrTy rawPtrDst = getAddressable(dPtr);
  RawPtrTy rawPtrSrc = getAddressable(sPtr);
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(m_slots[i - 1].MemCpy(rawPtrDst, rawPtrSrc, len,
                                            memTrsfrRead.getSlot(i),
                                            memRead.getSlot(i), align));
  }
  return mkFatMem(memVals);
}

/// \brief Executes symbolic memcpy from physical memory with concrete
/// length
template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::MemFill(PtrTy dPtr, char *sPtr, unsigned len,
                              MemValTy mem, uint32_t align) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(
      m_main.MemFill(mkMainPtr(dPtr), sPtr, len, mkMainMem(mem), align));
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(mem.getSlot(i));
  }
  return mkFatMem(memVals);
}

/// \brief Executes inttoptr conversion
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::inttoptr(Expr intVal, const Type &intTy,
                               const Type &ptrTy) const {
  return mkFatPtr(m_main.inttoptr(intVal, intTy, ptrTy));
}

/// \brief Executes ptrtoint conversion. This only converts the raw ptr to
/// int.
template <class T>
Expr FatMemManagerCore<T>::ptrtoint(PtrTy ptr, const Type &ptrTy,
                                    const Type &intTy) const {
  return m_main.ptrtoint(mkMainPtr(ptr), ptrTy, intTy);
}

template <class T> Expr FatMemManagerCore<T>::ptrUlt(PtrTy p1, PtrTy p2) const {
  return m_main.ptrUlt(mkMainPtr(p1), mkMainPtr(p2));
}

template <class T> Expr FatMemManagerCore<T>::ptrSlt(PtrTy p1, PtrTy p2) const {
  return m_main.ptrSlt(mkMainPtr(p1), mkMainPtr(p2));
}
template <class T> Expr FatMemManagerCore<T>::ptrUle(PtrTy p1, PtrTy p2) const {
  return m_main.ptrUle(mkMainPtr(p1), mkMainPtr(p2));
}
template <class T> Expr FatMemManagerCore<T>::ptrSle(PtrTy p1, PtrTy p2) const {
  return m_main.ptrSle(mkMainPtr(p1), mkMainPtr(p2));
}
template <class T> Expr FatMemManagerCore<T>::ptrUgt(PtrTy p1, PtrTy p2) const {
  return m_main.ptrUgt(mkMainPtr(p1), mkMainPtr(p2));
}
template <class T> Expr FatMemManagerCore<T>::ptrSgt(PtrTy p1, PtrTy p2) const {
  return m_main.ptrSgt(mkMainPtr(p1), mkMainPtr(p2));
}
template <class T> Expr FatMemManagerCore<T>::ptrUge(PtrTy p1, PtrTy p2) const {
  return m_main.ptrUge(mkMainPtr(p1), mkMainPtr(p2));
}
template <class T> Expr FatMemManagerCore<T>::ptrSge(PtrTy p1, PtrTy p2) const {
  return m_main.ptrSge(mkMainPtr(p1), mkMainPtr(p2));
}

/// \brief Checks if two pointers are equal.
template <class T> Expr FatMemManagerCore<T>::ptrEq(PtrTy p1, PtrTy p2) const {
  return m_main.ptrEq(mkMainPtr(p1), mkMainPtr(p2));
}
template <class T> Expr FatMemManagerCore<T>::ptrNe(PtrTy p1, PtrTy p2) const {
  return m_main.ptrNe(mkMainPtr(p1), mkMainPtr(p2));
}

template <class T> Expr FatMemManagerCore<T>::ptrSub(PtrTy p1, PtrTy p2) const {
  return m_main.ptrSub(mkMainPtr(p1), mkMainPtr(p2));
}

/// \brief Computes a pointer corresponding to the gep instruction
template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::gep(PtrTy ptr, gep_type_iterator it,
                          gep_type_iterator end) const {
  // Here the resultant pointer automatically gets the same slot(s) data
  // as the original. Therefore we don't require the client to manually
  // update slot(s) data after a gep call.
  MainPtrTy mainPtr = m_main.gep(ptr.getMain(), it, end);
  return updateFatPtr(mainPtr, ptr);
}

/// \brief Called when a function is entered for the first time
template <class T>
void FatMemManagerCore<T>::onFunctionEntry(const Function &fn) {
  m_main.onFunctionEntry(fn);
  for (auto memMgr : m_slots) {
    memMgr.onFunctionEntry(fn);
  }
}

/// \brief Called when a module entered for the first time
template <class T> void FatMemManagerCore<T>::onModuleEntry(const Module &M) {
  m_main.onModuleEntry(M);
  for (unsigned i = 0; i < g_FatMemSlots; i++) {
    m_slots[i].onModuleEntry(M);
  }
}

/// \brief Debug helper
template <class T> void FatMemManagerCore<T>::dumpGlobalsMap() {
  m_main.dumpGlobalsMap();
}

template <class T>
std::pair<char *, unsigned> FatMemManagerCore<T>::getGlobalVariableInitValue(
    const llvm::GlobalVariable &gv) {
  // TODO: do we need to make a union
  return m_main.getGlobalVariableInitValue(gv);
}

template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::zeroedMemory() const {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(m_main.zeroedMemory());
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(m_slots[i - 1].zeroedMemory());
  }
  return mkFatMem(memVals);
}

/// \brief get fat data in ith fat slot.
template <class T>
Expr FatMemManagerCore<T>::getFatData(PtrTy p, unsigned SlotIdx) {
  return p.getSlot(1 + SlotIdx);
}

template <class T>
typename FatMemManagerCore<T>::PtrTy
FatMemManagerCore<T>::setFatData(PtrTy p, unsigned slotIdx, Expr data) {
  assert(slotIdx < g_FatMemSlots);
  llvm::SmallVector<AnyPtrTy, 8> ptrVals;
  ptrVals.push_back(p.getMain());
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    if (slotIdx + 1 == i) {
      ptrVals.push_back(data);
    } else {
      ptrVals.push_back(p.getSlot(i));
    }
  }
  return mkFatPtr(ptrVals);
}

template <class T>
typename FatMemManagerCore<T>::RawPtrTy
FatMemManagerCore<T>::getAddressable(PtrTy p) const {
  return m_main.getAddressable(p.getMain());
}

template <class T> bool FatMemManagerCore<T>::isPtrTyVal(Expr e) const {
  // struct with raw ptr + fat slots
  return e && strct::isStructVal(e) && e->arity() == (1 + g_FatMemSlots);
}

template <class T> bool FatMemManagerCore<T>::isMemVal(Expr e) const {
  // struct with raw ptr + fat slots
  return e && strct::isStructVal(e) && e->arity() == (1 + g_FatMemSlots);
}

template <class T>
Expr FatMemManagerCore<T>::isMetadataSet(MetadataKind kind, PtrTy ptr,
                                         MemValTy mem) {
  // The width of the value will be wordSz
  Expr val = getMetadata(kind, ptr, mem, 1);
  if (val == Expr()) {
    return m_ctx.alu().getTrue();
  }
  auto sentinel = m_ctx.alu().ui(1, getMetadataMemWordSzInBits());
  return m_ctx.alu().doEq(val, sentinel, getMetadataMemWordSzInBits());
}

template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::memsetMetadata(MetadataKind kind, PtrTy ptr,
                                     unsigned int len, MemValTy memIn,
                                     unsigned int val) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(
      m_main.memsetMetadata(kind, ptr.getMain(), len, memIn.getMain(), val));
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(memIn.getSlot(i));
  }
  return mkFatMem(memVals);
}

template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::memsetMetadata(MetadataKind kind, PtrTy ptr, Expr len,
                                     MemValTy memIn, unsigned int val) {
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  memVals.push_back(
      m_main.memsetMetadata(kind, ptr.getMain(), len, memIn.getMain(), val));
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(memIn.getSlot(i));
  }
  return mkFatMem(memVals);
}

template <class T>
Expr FatMemManagerCore<T>::getMetadata(MetadataKind kind, PtrTy ptr,
                                       MemValTy memIn, unsigned int byteSz) {
  return m_main.getMetadata(kind, ptr.getMain(), memIn.getMain(), byteSz);
}

template <class T>
unsigned int FatMemManagerCore<T>::getMetadataMemWordSzInBits() {
  return m_main.getMetadataMemWordSzInBits();
}

template <class T> size_t FatMemManagerCore<T>::getNumOfMetadataSlots() {
  return m_main.getNumOfMetadataSlots();
}

template <class T>
typename FatMemManagerCore<T>::MemValTy
FatMemManagerCore<T>::setMetadata(MetadataKind kind, PtrTy ptr, MemValTy mem,
                                  Expr val) {
  if (!m_ctx.isTrackingOn() && kind != MetadataKind::ALLOC) {
    LOG("opsem.memtrack.verbose",
        WARN << "Ignoring setMetadata();Memory tracking is off"
             << "\n";);
    return mem;
  }
  llvm::SmallVector<AnyMemValTy, 8> memVals;
  auto mainOut = m_main.setMetadata(kind, ptr.getMain(), mem.getMain(), val);
  memVals.push_back(mainOut);
  for (unsigned i = 1; i <= g_FatMemSlots; i++) {
    memVals.push_back(mem.getSlot(i));
  }
  return mkFatMem(memVals);
}

template <class T>
Expr FatMemManagerCore<T>::isDereferenceable(PtrTy p, Expr byteSz) {
  return m_main.isDereferenceable(p.getMain(), byteSz);
}
// };

template <class T>
FatMemManagerCore<T>::FatMemManagerCore(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                        unsigned ptrSz, unsigned wordSz,
                                        bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to T MemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_fatMemBaseName("sea.fatmem"),
      m_slots(FatMemSlots,
              RawMemManager(sem, ctx, ptrSz, g_slotByteWidth, useLambdas,
                            /* ignoreAlignment =*/true)) {
  g_FatMemSlots = FatMemSlots;
}

OpSemMemManager *mkFatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas) {
  return new OpSemMemManagerMixin<FatMemManagerCore<RawMemManager>>(
      sem, ctx, ptrSz, wordSz, useLambdas);
}

// FatMemManager with ExtraWide and Tracking components
OpSemMemManager *mkFatEWWTManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                  unsigned ptrSz, unsigned wordSz,
                                  bool useLambdas) {
  return new FatEWWTMemManager(sem, ctx, ptrSz, wordSz, useLambdas);
}

// FatMemManager with ExtraWide component
OpSemMemManager *mkFatEWWManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas) {
  return new FatEWWMemManager(sem, ctx, ptrSz, wordSz, useLambdas);
}

template class FatMemManagerCore<RawMemManager>;
template class OpSemMemManagerMixin<FatMemManagerCore<OpSemMemManagerMixin<
    ExtraWideMemManagerCore<OpSemMemManagerMixin<TrackingRawMemManager>>>>>;

} // namespace details
} // namespace seahorn
