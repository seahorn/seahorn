#include "BvOpSem2RawMemMgr.hh"
#include "BvOpSem2Context.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {
enum class MemAllocatorKind { NORMAL_ALLOCATOR, STATIC_ALLOCATOR };
}
} // namespace seahorn

static llvm::cl::opt<enum seahorn::details::MemAllocatorKind> MemAllocatorOpt(
    "sea-opsem-allocator", llvm::cl::desc("A choice for memory allocator"),
    llvm::cl::values(
        clEnumValN(seahorn::details::MemAllocatorKind::NORMAL_ALLOCATOR,
                   "normal", "Regular allocator"),
        clEnumValN(seahorn::details::MemAllocatorKind::STATIC_ALLOCATOR,
                   "static", "Static pre-allocation")),
    llvm::cl::init(seahorn::details::MemAllocatorKind::NORMAL_ALLOCATOR));

static llvm::cl::opt<bool> IgnoreAlignmentOpt(
    "horn-opsem-ignore-alignment", // rename into sea-opsem-ignore-alignment
                                   // when supported
    llvm::cl::desc("Ignore alignment information and assume that all memory "
                   "operations are word aligned"),
    llvm::cl::init(false));

static llvm::cl::opt<bool> ExplicitSp0(
    "horn-explicit-sp0",
    llvm::cl::desc(
        "Set initial stack pointer (sp0) to an explicit numeric constant"),
    llvm::cl::init(false));
namespace seahorn {
namespace details {

OpSemMemManager *mkRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas) {
  return new RawMemManager(
      sem, ctx, ptrSz, wordSz, useLambdas,
      IgnoreAlignmentOpt /* use flag if user did not provide this value */);
};

OpSemMemManager *mkRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas, bool ignoreAlignment) {
  return new RawMemManager(sem, ctx, ptrSz, wordSz, useLambdas,
                           ignoreAlignment);
};

using PtrTy = RawMemManager::PtrTy;

RawMemManager::RawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                             unsigned ptrSz, unsigned wordSz, bool useLambdas)
    : RawMemManager::RawMemManager(sem, ctx, ptrSz, wordSz, useLambdas,
                                   IgnoreAlignmentOpt) {}

RawMemManager::RawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                             unsigned ptrSz, unsigned wordSz, bool useLambdas,
                             bool ignoreAlignment)
    : OpSemMemManager(sem, ctx, ptrSz, wordSz, ignoreAlignment),
      m_freshPtrName(mkTerm<std::string>("sea.ptr", m_efac)), m_id(0) {
  if (MemAllocatorOpt == MemAllocatorKind::NORMAL_ALLOCATOR)
    m_allocator = mkNormalOpSemAllocator(*this);
  else if (MemAllocatorOpt == MemAllocatorKind::STATIC_ALLOCATOR)
    m_allocator = mkStaticOpSemAllocator(*this);
  assert(m_allocator);

  m_nullPtr = m_ctx.alu().si(0UL, ptrSzInBits());
  m_sp0 = bind::mkConst(mkTerm<std::string>("sea.sp0", m_efac), ptrSort());
  m_ctx.declareRegister(m_sp0);

  if (ExplicitSp0)
    m_sp0 = m_ctx.alu().si(0xC0000000, this->ptrSzInBits());

  if (useLambdas)
    m_memRepr = std::make_unique<OpSemMemLambdaRepr>(*this, ctx);
  else
    m_memRepr = std::make_unique<OpSemMemArrayRepr>(*this, ctx);
}

/// \brief Creates a non-deterministic pointer that is aligned
///
/// Top bits of the pointer are named by \p name and last \c log2(align) bits
/// are set to zero
PtrTy RawMemManager::mkAlignedPtr(Expr name, uint32_t align) const {
  unsigned alignBits = llvm::Log2_32(align);
  Expr wordPtr =
      bind::mkConst(name, m_ctx.alu().intTy(ptrSzInBits() - alignBits));
  return bv::concat(wordPtr, bv::bvnum(0UL, alignBits, m_efac));
}

/// \brief Returns sort of a pointer register for an instruction
Expr RawMemManager::mkPtrRegisterSort(const Instruction &inst) const {
  const Type *ty = inst.getType();
  assert(ty);
  unsigned sz = m_sem.sizeInBits(*ty);
  assert(ty->isPointerTy());
  LOG(
      "opsem", if (sz != ptrSzInBits()) {
        ERR << "Unexpected size of type: " << *ty << " of instruction " << inst
            << "\n"
            << "sz is " << sz << " and ptrSzInBits is " << ptrSzInBits()
            << "\n";
      });
  assert(m_sem.sizeInBits(*ty) == ptrSzInBits());

  // return m_ctx.alu().intTy(m_sem.sizeInBits(*ty));
  return ptrSort();
}

/// \brief Returns sort of a pointer register for a function pointer
Expr RawMemManager::mkPtrRegisterSort(const Function &fn) const {
  return ptrSort();
}

/// \brief Returns sort of memory-holding register for an instruction
Expr RawMemManager::mkMemRegisterSort(const Instruction &inst) const {
  Expr valTy = m_ctx.alu().intTy(wordSzInBits());
  return sort::arrayTy(ptrSort(), valTy);
}

/// \brief Returns a fresh aligned pointer value
PtrTy RawMemManager::freshPtr() {
  Expr name = op::variant::variant(m_id++, m_freshPtrName);
  return mkAlignedPtr(name, m_alignment);
}

PtrTy RawMemManager::nullPtr() const { return m_nullPtr; }

/// \brief Allocates memory on the stack and returns a pointer to it
/// \param align is requested alignment. If 0, default alignment is used
PtrTy RawMemManager::salloc(unsigned bytes, uint32_t align) {
  assert(isa<AllocaInst>(m_ctx.getCurrentInst()));
  align = std::max(align, m_alignment);
  auto region = m_allocator->salloc(bytes, align);

  return mkStackPtr(region.second);
}

/// \brief Returns a pointer value for a given stack allocation
PtrTy RawMemManager::mkStackPtr(unsigned offset) {
  PtrTy res = m_sp0;
  if (m_ctx.isKnownRegister(res))
    res = m_ctx.read(m_sp0);
  res = m_ctx.alu().doSub(
      res, m_ctx.alu().si((unsigned long)offset, ptrSzInBits()), ptrSzInBits());
  return res;
}

/// \brief Allocates memory on the stack and returns a pointer to it
PtrTy RawMemManager::salloc(Expr elmts, unsigned typeSz, unsigned align) {
  align = std::max(align, m_alignment);

  // -- compute number of bytes needed
  Expr bytes = elmts;
  if (typeSz > 1) {
    // TODO: factor out multiplication and number creation
    bytes = m_ctx.alu().doMul(bytes, m_ctx.alu().si(typeSz, ptrSzInBits()),
                              ptrSzInBits());
  }

  // allocate
  auto region = m_allocator->salloc(bytes, align);

  // -- if allocation failed, return some pointer
  if (m_allocator->isBadAddrInterval(region)) {
    LOG("opsem", WARN << "imprecise handling of dynamically "
                      << "sized stack allocation of " << *elmts
                      << " elements of size" << typeSz << " bytes\n";);
    return freshPtr();
  }

  // -- have a good region, return pointer to it
  return mkStackPtr(region.second);
}

/// \brief Pointer to start of the heap
PtrTy RawMemManager::brk0Ptr() {
  return m_ctx.alu().si(m_allocator->brk0Addr(), ptrSzInBits());
}

/// \brief Allocates memory on the heap and returns a pointer to it
PtrTy RawMemManager::halloc(unsigned _bytes, unsigned align) {
  Expr res = freshPtr();

  unsigned bytes = llvm::alignTo(_bytes, std::max(align, m_alignment));

  auto stackRange = m_allocator->getStackRange();
  // -- pointer is in the heap: between brk at the beginning and end of stack
  m_ctx.addSide(
      ptrUlt(res, m_ctx.alu().si(stackRange.first - bytes, ptrSzInBits())));
  m_ctx.addSide(ptrUgt(res, brk0Ptr()));
  return res;
}

/// \brief Allocates memory on the heap and returns pointer to it
PtrTy RawMemManager::halloc(Expr bytes, unsigned align) {
  Expr res = freshPtr();

  auto stackRange = m_allocator->getStackRange();
  // -- pointer is in the heap: between brk at the beginning and end of stack
  m_ctx.addSide(ptrUlt(res, m_ctx.alu().si(stackRange.first, ptrSzInBits())));
  m_ctx.addSide(ptrUgt(res, brk0Ptr()));
  // TODO: take size of pointer into account,
  // it cannot be that close to the stack
  return res;
}

/// \brief Allocates memory in global (data/bss) segment for given global
PtrTy RawMemManager::galloc(const GlobalVariable &gv, unsigned align) {
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  auto range = m_allocator->galloc(gv, gvSz, std::max(align, m_alignment));
  return m_ctx.alu().si(range.first, ptrSzInBits());
}

/// \brief Allocates memory in code segment for the code of a given function
PtrTy RawMemManager::falloc(const Function &fn) {
  auto range = m_allocator->falloc(fn, m_alignment);
  return m_ctx.alu().si(range.first, ptrSzInBits());
}

/// \brief Returns a function pointer value for a given function
PtrTy RawMemManager::getPtrToFunction(const Function &F) {
  return m_ctx.alu().si(m_allocator->getFunctionAddr(F, m_alignment),
                        ptrSzInBits());
}

/// \brief Returns a pointer to a global variable
PtrTy RawMemManager::getPtrToGlobalVariable(const GlobalVariable &gv) {
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  return m_ctx.alu().si(
      m_allocator->getGlobalVariableAddr(gv, gvSz, m_alignment), ptrSzInBits());
}

void RawMemManager::initGlobalVariable(const GlobalVariable &gv) const {
  if (!gv.hasInitializer()) {
    LOG("opsem", WARN << "GV without an initializer: " << gv << "\n";);
    return;
  }

  ConstantExprEvaluator ce(m_sem.getDataLayout());
  ce.setContext(m_ctx);
  char *bytes = m_allocator->getGlobalVariableMem(gv);
  LOG("opsem", if (!bytes) ERR
                   << "Unexpected nullptr storage for global: " << gv << "\n";);
  assert(bytes);
  ce.initMemory(gv.getInitializer(), bytes);
}

/// \brief Pointers have word address (high) and byte offset (low); returns
/// number of bits for byte offset
///
/// \return 0 if unsupported word size
unsigned RawMemManager::getByteAlignmentBits() {
  switch (wordSzInBytes()) {
  // cases where ptrs are known to use a certain number of bits to denote byte
  // offset
  //   and the rest to denote word aligned address
  case 1:
    return 0;
  case 2:
    return 1;
  case 4:
    return 2;
  case 8:
    return 3;
  default:
    WARN << "unsupported word size: " << wordSzInBytes()
         << " unaligned reads may not work as intended\n";
    return 0;
  }
}

/// \brief Fixes the type of a havoced value to mach the representation used
/// by mem repr.
///
/// \param reg
/// \param val
/// \return the coerced value.
Expr RawMemManager::coerce(Expr sort, Expr val) {
  return m_memRepr->coerce(sort, val);
}

/// \brief Symbolic instructions to load a byte from memory, using word
/// address and byte address
///
/// \param[in] mem memory being accessed
/// \param[in] address pointer being accessed, unaligned
/// \param[in] offsetBits number of bits at end of pointers reserved for byte
///            address
/// \return symbolic value of the byte at the specified address
Expr RawMemManager::extractUnalignedByte(Expr mem, PtrTy address,
                                         unsigned offsetBits) {
  // pointers are partitioned into word address (high bits) and offset (low
  // bits)
  PtrTy wordAddress = bv::extract(ptrSzInBits() - 1, offsetBits, address);
  PtrTy byteOffset = bv::extract(offsetBits - 1, 0, address);

  // aligned ptr is address with offset bits truncated to 0
  PtrTy alignedPtr =
      bv::concat(wordAddress, bv::bvnum(0L, offsetBits, address->efac()));
  Expr alignedWord = m_memRepr->loadAlignedWordFromMem(alignedPtr, mem);

  byteOffset = bv::zext(byteOffset, wordSzInBits() - 3);
  // (x << 3) to get bit offset; zero extend to maintain word size
  PtrTy bitOffset = bv::concat(byteOffset, bv::bvnum(0U, 3, address->efac()));

  return bv::extract(7, 0, mk<BLSHR>(alignedWord, bitOffset));
}

/// \brief Loads an integer of a given size from memory register
///
/// \param[in] ptr pointer being accessed
/// \param[in] memReg memory register into which \p ptr points
/// \param[in] byteSz size of the integer in bytes
/// \param[in] align known alignment of \p ptr
/// \return symbolic value of the read integer
Expr RawMemManager::loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                                   uint64_t align) {
  SmallVector<Expr, 16> words;
  unsigned offsetBits = getByteAlignmentBits();
  if (!m_ignoreAlignment && offsetBits != 0 && align % wordSzInBytes() != 0) {
    for (unsigned i = 0; i < byteSz; i++) {
      Expr byteOfWord = extractUnalignedByte(mem, ptrAdd(ptr, i), offsetBits);
      words.push_back(byteOfWord);
    }
  } else {
    // -- read all words
    for (unsigned i = 0; i < byteSz; i += wordSzInBytes()) {
      words.push_back(m_memRepr->loadAlignedWordFromMem(ptrAdd(ptr, i), mem));
    }
  }

  assert(!words.empty());

  // -- concatenate the words together into a single value
  Expr res;
  for (Expr &w : words)
    res = res ? bv::concat(w, res) : w;

  assert(res);
  // -- extract actual bytes read (if fewer than word)
  if (byteSz < wordSzInBytes())
    res = bv::extract(byteSz * 8 - 1, 0, res);

  return res;
}

/// \brief Loads a pointer stored in memory
/// \sa loadIntFromMem
PtrTy RawMemManager::loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                                    uint64_t align) {
  return loadIntFromMem(ptr, mem, byteSz, align);
}

/// \brief Pointer addition with numeric offset
PtrTy RawMemManager::ptrAdd(PtrTy ptr, int32_t _offset) const {
  if (_offset == 0)
    return ptr;
  expr::mpz_class offset((signed long)_offset);
  return m_ctx.alu().doAdd(ptr, m_ctx.alu().si(offset, ptrSzInBits()),
                           ptrSzInBits());
}

/// \brief Pointer addition with symbolic offset
PtrTy RawMemManager::ptrAdd(PtrTy ptr, Expr offset) const {
  if (m_ctx.alu().isNum(offset)) {
    expr::mpz_class _offset = m_ctx.alu().toNum(offset);
    return ptrAdd(ptr, _offset.get_si());
  }
  return m_ctx.alu().doAdd(ptr, offset, ptrSzInBits());
}

/// \brief Stores an integer into memory
/// \param[in] ptr is the address at which _val will be stored
/// \param[in] _val is the value being written
/// \param[in] mem is the memory bank/register being written to
/// \param[in] byteSz is the size of _val in bytes (should be =< word size)
/// \param[in] align is the known alignment of the ptr
/// Returns an expression describing the state of memory in \c memReadReg
/// after the store
/// \sa loadIntFromMem
Expr RawMemManager::storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                                  unsigned byteSz, uint64_t align) {
  Expr val = _val;

  unsigned offsetBits = getByteAlignmentBits();
  bool wordAligned = offsetBits == 0 || align % wordSzInBytes() == 0;
  if (!m_ignoreAlignment && !wordAligned) {
    return storeUnalignedIntToMem(val, ptr, mem, byteSz);
  }

  SmallVector<Expr, 16> words;
  if (byteSz == wordSzInBytes()) {
    words.push_back(val);
  } else if (byteSz < wordSzInBytes()) {
    val = m_ctx.alu().doZext(val, wordSzInBits(), byteSz * 8);
    words.push_back(val);
  } else {
    for (unsigned i = 0; i < byteSz; i += wordSzInBytes()) {
      unsigned lowBit = i * 8;
      Expr slice = bv::extract(lowBit + wordSzInBits() - 1, lowBit, val);
      words.push_back(slice);
    }
  }

  Expr res;
  for (unsigned i = 0; i < words.size(); ++i) {
    res = m_memRepr->storeAlignedWordToMem(
        words[i], ptrAdd(ptr, i * wordSzInBytes()), ptrSort(), mem);
    mem = res;
  }

  return res;
}

/// \brief stores integer into memory, address is not word aligned
///
/// \sa storeIntToMem
Expr RawMemManager::storeUnalignedIntToMem(Expr val, PtrTy ptr, MemValTy mem,
                                           unsigned byteSz) {
  unsigned offsetBits = getByteAlignmentBits();
  assert(offsetBits != 0);

  // for each byte (i) in val, load word w of i from memory, update one byte
  // of w, write back result
  Expr res;
  for (unsigned i = 0; i < byteSz; i++) {
    PtrTy wordAddress =
        bv::extract(ptrSzInBits() - 1, offsetBits, ptrAdd(ptr, i));
    PtrTy byteOffset = bv::extract(offsetBits - 1, 0, ptrAdd(ptr, i));

    PtrTy alignedPtr =
        bv::concat(wordAddress, bv::bvnum(0L, offsetBits, ptr->efac()));
    Expr existingWord = m_memRepr->loadAlignedWordFromMem(alignedPtr, mem);

    unsigned lowBit = i * 8;
    Expr byteToStore = bv::extract(lowBit + 7, lowBit, val);

    Expr updatedWord = setByteOfWord(existingWord, byteToStore, byteOffset);
    res = m_memRepr->storeAlignedWordToMem(updatedWord, alignedPtr, ptrSort(),
                                           mem);
    mem = res;
  }

  return res;
}

/// \brief Given a word, updates a byte
///
/// \param word existing word
/// \param byteData updated byte
/// \param byteOffset symbolic pointer indicating which byte to update
/// \return updated word
Expr RawMemManager::setByteOfWord(Expr word, Expr byteData, PtrTy byteOffset) {
  // (x << 3) to get bit offset; zero extend to maintain word size
  byteOffset = bv::zext(byteOffset, wordSzInBits() - 3);
  PtrTy bitOffset =
      bv::concat(byteOffset, bv::bvnum(0U, 3, byteOffset->efac()));

  // set a byte of existing word to 0
  Expr lowestByteMask = bv::bvnum(0xffU, wordSzInBits(), word->efac());
  Expr addressByteMask = mk<BNOT>(mk<BSHL>(lowestByteMask, bitOffset));
  word = mk<BAND>(word, addressByteMask);

  // shift into position for zeroed part of existing word; mask and rewrite
  Expr shiftedByte = mk<BSHL>(bv::zext(byteData, wordSzInBits()), bitOffset);

  return mk<BOR>(word, shiftedByte);
}

/// \brief Stores a pointer into memory
/// \sa storeIntToMem
Expr RawMemManager::storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                                  unsigned byteSz, uint64_t align) {
  return storeIntToMem(val, ptr, mem, byteSz, align);
}

/// \brief Returns an expression corresponding to a load from memory
///
/// \param[in] ptr is the pointer being dereferenced
/// \param[in] mem is the memory value being read from
/// \param[in] ty is the type of value being loaded
/// \param[in] align is the known alignment of the load
Expr RawMemManager::loadValueFromMem(PtrTy ptr, MemValTy mem,
                                     const llvm::Type &ty, uint64_t align) {
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
    report_fatal_error(out.str());
  }
  return res;
}

Expr RawMemManager::storeValueToMem(Expr _val, PtrTy ptr, MemValTy mem,
                                    const llvm::Type &ty, uint32_t align) {
  assert(ptr);
  Expr val = _val;
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr->efac();

  Expr res;
  switch (ty.getTypeID()) {
  case Type::IntegerTyID:
    if (ty.getScalarSizeInBits() < byteSz * 8) {
      val = m_ctx.alu().doZext(val, byteSz * 8, ty.getScalarSizeInBits());
    }
    res = storeIntToMem(val, ptr, mem, byteSz, align);
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
    res = storePtrToMem(val, ptr, mem, byteSz, align);
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
Expr RawMemManager::MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                           uint32_t align) {
  return m_memRepr->MemSet(ptr, _val, len, mem, wordSzInBytes(), ptrSort(),
                           align);
}

/// \brief Executes symbolic memcpy with concrete length
Expr RawMemManager::MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len,
                           MemValTy memTrsfrRead, uint32_t align) {
  return m_memRepr->MemCpy(dPtr, sPtr, len, memTrsfrRead, wordSzInBytes(),
                           ptrSort(), align);
}

/// \brief Executes symbolic memcpy from physical memory with concrete length
Expr RawMemManager::MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                            uint32_t align) {
  // same alignment behavior as galloc - default is word size of machine, can
  // only be increased
  return m_memRepr->MemFill(dPtr, sPtr, len, mem, wordSzInBytes(), ptrSort(),
                            std::max(align, m_alignment));
}

/// \brief Executes inttoptr conversion
PtrTy RawMemManager::inttoptr(Expr intVal, const Type &intTy,
                              const Type &ptrTy) const {
  uint64_t intTySz = m_sem.sizeInBits(intTy);
  uint64_t ptrTySz = m_sem.sizeInBits(ptrTy);
  assert(ptrTySz == ptrSzInBits());

  Expr res = intVal;
  if (ptrTySz > intTySz)
    res = bv::zext(res, ptrTySz);
  else if (ptrTySz < intTySz)
    res = bv::extract(ptrTySz - 1, 0, res);
  return res;
}

Expr RawMemManager::ptrUlt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUlt(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrUle(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUle(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrSlt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSlt(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrSle(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSle(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrUgt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUgt(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrUge(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUge(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrSgt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSgt(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrSge(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSge(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrEq(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doEq(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrNe(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doNe(p1, p2, ptrSzInBits());
}
Expr RawMemManager::ptrSub(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSub(p1, p2, ptrSzInBits());
}
Expr RawMemManager::getFatData(PtrTy p, unsigned SlotIdx) {
  LOG("opsem", WARN << "getFatData() not implemented");
  return Expr();
}
Expr RawMemManager::setFatData(PtrTy p, unsigned SlotIdx, Expr data) {
  LOG("opsem", WARN << "setFatData() not implemented");
  return Expr();
}

Expr RawMemManager::isDereferenceable(PtrTy p, Expr byteSz) {
  LOG("opsem", ERR << "isDeferenceable() not implemented");
  return Expr();
}

/// \brief Executes ptrtoint conversion
Expr RawMemManager::ptrtoint(PtrTy ptr, const Type &ptrTy,
                             const Type &intTy) const {
  uint64_t ptrTySz = m_sem.sizeInBits(ptrTy);
  uint64_t intTySz = m_sem.sizeInBits(intTy);
  assert(ptrTySz == ptrSzInBits());

  Expr res = ptr;
  if (ptrTySz < intTySz)
    res = bv::zext(res, intTySz);
  else if (ptrTySz > intTySz)
    res = bv::extract(intTySz - 1, 0, res);
  return res;
}

/// \brief Computes a pointer corresponding to the gep instruction
PtrTy RawMemManager::gep(PtrTy ptr, gep_type_iterator it,
                         gep_type_iterator end) const {
  Expr offset = m_sem.symbolicIndexedOffset(it, end, m_ctx);
  return offset ? ptrAdd(ptr, offset) : Expr();
}

void RawMemManager::onModuleEntry(const Module &M) {
  return m_allocator->onModuleEntry(M);
}

/// \brief Called when a function is entered for the first time
void RawMemManager::onFunctionEntry(const Function &fn) {
  m_allocator->onFunctionEntry(fn);

  Expr res = m_sp0;
  if (m_ctx.isKnownRegister(res))
    res = m_ctx.read(m_sp0);

  // align of semantic_word_size, or 4 if it's less than 4
  unsigned offsetBits = 2;
  switch (wordSzInBytes()) {
  case 8:
    offsetBits = 3;
  }
  m_ctx.addDef(bv::bvnum(0U, offsetBits, m_efac),
               bv::extract(offsetBits - 1, 0, res));

  auto stackRange = m_allocator->getStackRange();

  // XXX Currently hard coded for typical 32bit system
  // -- 3GB upper limit
  m_ctx.addSide(ptrUle(res, m_ctx.alu().si(stackRange.second, ptrSzInBits())));
  // -- 9MB stack
  m_ctx.addSide(ptrUge(res, m_ctx.alu().si(stackRange.first, ptrSzInBits())));
}

Expr RawMemManager::zeroedMemory() const {
  return m_memRepr->FilledMemory(ptrSort(), m_ctx.alu().si(0, wordSzInBits()));
}
OpSemAllocator &RawMemManager::getMAllocator() const { return *m_allocator; }
bool RawMemManager::ignoreAlignment() const { return m_ignoreAlignment; }
} // namespace details
} // namespace seahorn
