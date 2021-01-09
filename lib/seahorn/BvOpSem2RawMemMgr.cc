#include "BvOpSem2RawMemMgr.hh"
#include "BvOpSem2Allocators.hh"
#include "BvOpSem2Context.hh"
#include "BvOpSem2MemManagerMixin.hh"
#include "BvOpSem2MemRepr.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/CommandLine.h"

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

static llvm::cl::opt<unsigned> MemCpyUnrollCount(
    "horn-array-sym-memcpy-unroll-count",
    llvm::cl::desc("When using array repr of memory; this sets the loop unroll "
                   "count for symbolic memcpy"),
    llvm::cl::init(16));

static llvm::cl::opt<unsigned> MaxSymbAllocSz(
    "horn-opsem-max-symb-alloc",
    llvm::cl::desc("Maximum expected size of any symbolic allocation"),
    llvm::cl::init(4096));
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

using PtrTy = RawMemManagerCore::PtrTy;

RawMemManagerCore::RawMemManagerCore(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                     unsigned ptrSz, unsigned wordSz,
                                     bool useLambdas)
    : RawMemManagerCore::RawMemManagerCore(sem, ctx, ptrSz, wordSz, useLambdas,
                                           IgnoreAlignmentOpt) {}

RawMemManagerCore::RawMemManagerCore(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                     unsigned ptrSz, unsigned wordSz,
                                     bool useLambdas, bool ignoreAlignment)
    : MemManagerCore(sem, ctx, ptrSz, wordSz, ignoreAlignment),
      m_freshPtrName(mkTerm<std::string>("sea.ptr", m_efac)), m_id(0),
      m_nullPtr(PtrTy(m_ctx.alu().ui(0UL, ptrSizeInBits()))),
      m_sp0(PtrTy(bind::mkConst(mkTerm<std::string>("sea.sp0", m_efac),
                                ptrSort().toExpr()))) {
  if (MemAllocatorOpt == MemAllocatorKind::NORMAL_ALLOCATOR)
    m_allocator = mkNormalOpSemAllocator(*this, MaxSymbAllocSz);
  else if (MemAllocatorOpt == MemAllocatorKind::STATIC_ALLOCATOR)
    m_allocator = mkStaticOpSemAllocator(*this, MaxSymbAllocSz);
  assert(m_allocator);
  m_ctx.declareRegister(m_sp0.toExpr());

  if (ExplicitSp0)
    m_sp0 = PtrTy(m_ctx.alu().ui(0xC0000000, this->ptrSizeInBits()));

  if (useLambdas)
    m_memRepr = std::make_unique<OpSemMemLambdaRepr>(*this, ctx);
  else
    m_memRepr =
        std::make_unique<OpSemMemArrayRepr>(*this, ctx, MemCpyUnrollCount);
}

/// \brief Creates a non-deterministic pointer that is aligned
///
/// Top bits of the pointer are named by \p name and last \c log2(align) bits
/// are set to zero
PtrTy RawMemManagerCore::mkAlignedPtr(Expr name, uint32_t align) const {
  unsigned alignBits = llvm::Log2_32(align);
  Expr wordPtr =
      bind::mkConst(name, m_ctx.alu().intTy(ptrSizeInBits() - alignBits));
  // assuming that we don't lose information by treating int as ptr width
  return PtrTy(
      m_ctx.alu().Concat({wordPtr, ptrSizeInBits()} /* high */,
                         {bv::bvnum(0UL, alignBits, m_efac), alignBits}));
}

/// \brief Returns sort of a pointer register for an instruction
RawMemManagerCore::PtrSortTy
RawMemManagerCore::mkPtrRegisterSort(const Instruction &inst) const {
  const Type *ty = inst.getType();
  assert(ty);
  unsigned sz = m_sem.sizeInBits(*ty);
  assert(ty->isPointerTy());
  LOG(
      "opsem", if (sz != ptrSizeInBits()) {
        ERR << "Unexpected size of type: " << *ty << " of instruction " << inst
            << "\n"
            << "sz is " << sz << " and ptrSizeInBits is " << ptrSizeInBits()
            << "\n";
      });
  assert(m_sem.sizeInBits(*ty) == ptrSizeInBits());

  // return m_ctx.alu().intTy(m_sem.sizeInBits(*ty));
  return ptrSort();
}

/// \brief Returns sort of a pointer register for a function pointer
RawMemManagerCore::PtrSortTy
RawMemManagerCore::mkPtrRegisterSort(const Function &fn) const {
  return ptrSort();
}

/// \brief Returns sort of memory-holding register for an instruction
RawMemManagerCore::MemSortTy
RawMemManagerCore::mkMemRegisterSort(const Instruction &inst) const {
  Expr valTy = m_ctx.alu().intTy(wordSizeInBits());
  // index type is a ptr, valTy is a word in memory
  return MemSortTy(sort::arrayTy(ptrSort().toExpr(), valTy));
}

/// \brief Returns a fresh aligned pointer value
PtrTy RawMemManagerCore::freshPtr() {
  Expr name = op::variant::variant(m_id++, m_freshPtrName);
  return mkAlignedPtr(name, m_alignment);
}

PtrTy RawMemManagerCore::nullPtr() const { return m_nullPtr; }

/// \brief Allocates memory on the stack and returns a pointer to it
/// \param align is requested alignment. If 0, default alignment is used
PtrTy RawMemManagerCore::salloc(unsigned bytes, uint32_t align) {
  assert(isa<AllocaInst>(m_ctx.getCurrentInst()));
  align = std::max(align, m_alignment);
  auto region = m_allocator->salloc(bytes, align);

  return mkStackPtr(region.second);
}

/// \brief Returns a pointer value for a given stack allocation
PtrTy RawMemManagerCore::mkStackPtr(unsigned offset) {
  Expr res = m_sp0.toExpr();
  if (m_ctx.isKnownRegister(res))
    res = m_ctx.read(m_sp0.toExpr());
  res = m_ctx.alu().doSub(res, m_ctx.alu().ui(offset, ptrSizeInBits()),
                          ptrSizeInBits());
  return PtrTy(res);
}

/// \brief Allocates memory on the stack and returns a pointer to it
PtrTy RawMemManagerCore::salloc(Expr elmts, unsigned typeSz, unsigned align) {
  align = std::max(align, m_alignment);

  // -- compute number of bytes needed
  Expr bytes = elmts;
  if (typeSz > 1) {
    // TODO: factor out multiplication and number creation
    bytes = m_ctx.alu().doMul(bytes, m_ctx.alu().ui(typeSz, ptrSizeInBits()),
                              ptrSizeInBits());
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
PtrTy RawMemManagerCore::brk0Ptr() {
  return PtrTy(m_ctx.alu().ui(m_allocator->brk0Addr(), ptrSizeInBits()));
}

/// \brief Allocates memory on the heap and returns a pointer to it
PtrTy RawMemManagerCore::halloc(unsigned _bytes, unsigned align) {
  PtrTy res = freshPtr();

  unsigned bytes = llvm::alignTo(_bytes, std::max(align, m_alignment));

  auto stackRange = m_allocator->getStackRange();
  // -- pointer is in the heap: between brk at the beginning and end of stack
  m_ctx.addSide(ptrUlt(
      res, PtrTy(m_ctx.alu().ui(stackRange.first - bytes, ptrSizeInBits()))));
  m_ctx.addSide(ptrUgt(res, brk0Ptr()));
  return res;
}

/// \brief Allocates memory on the heap and returns pointer to it
PtrTy RawMemManagerCore::halloc(Expr bytes, unsigned align) {
  PtrTy res = freshPtr();

  auto stackRange = m_allocator->getStackRange();
  // -- pointer is in the heap: between brk at the beginning and end of stack
  m_ctx.addSide(
      ptrUlt(res, PtrTy(m_ctx.alu().si(stackRange.first, ptrSizeInBits()))));
  m_ctx.addSide(ptrUgt(res, brk0Ptr()));
  // TODO: take size of pointer into account,
  // it cannot be that close to the stack
  return res;
}

/// \brief Allocates memory in global (data/bss) segment for given global
PtrTy RawMemManagerCore::galloc(const GlobalVariable &gv, unsigned align) {
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  auto range = m_allocator->galloc(gv, gvSz, std::max(align, m_alignment));
  return PtrTy(m_ctx.alu().ui(range.first, ptrSizeInBits()));
}

/// \brief Allocates memory in code segment for the code of a given function
PtrTy RawMemManagerCore::falloc(const Function &fn) {
  auto range = m_allocator->falloc(fn, m_alignment);
  return PtrTy(m_ctx.alu().ui(range.first, ptrSizeInBits()));
}

/// \brief Returns a function pointer value for a given function
PtrTy RawMemManagerCore::getPtrToFunction(const Function &F) {
  return PtrTy(m_ctx.alu().ui(m_allocator->getFunctionAddr(F, m_alignment),
                              ptrSizeInBits()));
}

/// \brief Returns a pointer to a global variable
PtrTy RawMemManagerCore::getPtrToGlobalVariable(const GlobalVariable &gv) {
  uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
  return PtrTy(
      m_ctx.alu().ui(m_allocator->getGlobalVariableAddr(gv, gvSz, m_alignment),
                     ptrSizeInBits()));
}

void RawMemManagerCore::initGlobalVariable(const GlobalVariable &gv) const {
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
unsigned RawMemManagerCore::getByteAlignmentBits() {
  switch (wordSizeInBytes()) {
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
    WARN << "unsupported word size: " << wordSizeInBytes()
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
Expr RawMemManagerCore::coerce(Expr sort, Expr val) {
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
Expr RawMemManagerCore::extractUnalignedByte(MemValTy mem, const PtrTy &address,
                                             unsigned offsetBits) {
  // pointers are partitioned into word address (high bits) and offset (low
  // bits)
  Expr wordAddress =
      m_ctx.alu().Extract({address.toExpr(), ptrSizeInBits()},
                          offsetBits /* low */, ptrSizeInBits() - 1 /* high */);
  Expr byteOffset = m_ctx.alu().Extract({address.toExpr(), ptrSizeInBits()},
                                        0 /* low */, offsetBits - 1 /* high */);

  // aligned ptr is address with offset bits truncated to 0
  PtrTy alignedPtr = PtrTy(
      m_ctx.alu().Concat({wordAddress, ptrSizeInBits()} /* high */,
                         {bv::bvnum(0L, offsetBits, address.toExpr()->efac()),
                          offsetBits} /* low */));
  Expr alignedWord = m_memRepr->loadAlignedWordFromMem(alignedPtr, mem);

  byteOffset =
      m_ctx.alu().doZext(byteOffset, wordSizeInBits() - 3, ptrSizeInBits());
  // (x << 3) to get bit offset; zero extend to maintain word size
  Expr bitOffset = m_ctx.alu().Concat(
      {byteOffset, ptrSizeInBits()} /* high */,
      {bv::bvnum(0U, 3, address.toExpr()->efac()), 3} /* low */);
  return m_ctx.alu().Extract(
      {mk<BLSHR>(alignedWord, bitOffset), wordSizeInBits()}, 0 /* low */,
      7 /* high */);
}

/// \brief Loads an integer of a given size from memory register
///
/// \param[in] ptr pointer being accessed
/// \param[in] memReg memory register into which \p ptr points
/// \param[in] byteSz size of the integer in bytes
/// \param[in] align known alignment of \p ptr (in bytes)
/// \return symbolic value of the read integer
Expr RawMemManagerCore::loadIntFromMem(const PtrTy &ptr, const MemValTy &mem,
                                       unsigned byteSz, uint64_t align) {
  SmallVector<Expr, 16> words;
  unsigned offsetBits = getByteAlignmentBits();
  if (!m_ignoreAlignment && offsetBits != 0 && align % wordSizeInBytes() != 0) {
    for (unsigned i = 0; i < byteSz; i++) {
      Expr byteOfWord = extractUnalignedByte(mem, ptrAdd(ptr, i), offsetBits);
      words.push_back(byteOfWord);
    }
  } else {
    // -- read all words
    for (unsigned i = 0; i < byteSz; i += wordSizeInBytes()) {
      words.push_back(m_memRepr->loadAlignedWordFromMem(ptrAdd(ptr, i), mem));
    }
  }

  assert(!words.empty());

  // -- concatenate the words together into a single value
  Expr res;
  size_t res_size = 0;
  for (Expr &w : words) {
    res = res ? m_ctx.alu().Concat({w, wordSizeInBits()} /* high */,
                                   {res, res_size} /* low */)
              : w;
    res_size = res_size + wordSizeInBits();
  }
  assert(res);
  // -- extract actual bytes read (if fewer than word)
  if (byteSz < wordSizeInBytes())
    res = m_ctx.alu().Extract({res, res_size}, 0 /* low 8 */,
                              byteSz * 8 - 1 /* high */);

  return res;
}

/// \brief Loads a pointer stored in memory
/// \sa loadIntFromMem
PtrTy RawMemManagerCore::loadPtrFromMem(const PtrTy &ptr, const MemValTy &mem,
                                        unsigned byteSz, uint64_t align) {
  return PtrTy(loadIntFromMem(ptr, mem, byteSz, align));
}

/// \brief Pointer addition with numeric offset
PtrTy RawMemManagerCore::ptrAdd(PtrTy ptr, int32_t offset) const {
  if (offset == 0)
    return ptr;
  return PtrTy(m_ctx.alu().doAdd(
      ptr.toExpr(), m_ctx.alu().si(offset, ptrSizeInBits()), ptrSizeInBits()));
}

/// \brief Pointer addition with symbolic offset
PtrTy RawMemManagerCore::ptrAdd(const PtrTy &ptr, const Expr offset) const {
  if (m_ctx.alu().isNum(offset)) {
    expr::mpz_class _offset = m_ctx.alu().toNum(offset);
    return ptrAdd(ptr, _offset.get_si());
  }
  return PtrTy(m_ctx.alu().doAdd(ptr.toExpr(), offset, ptrSizeInBits()));
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
RawMemManagerCore::MemValTy
RawMemManagerCore::storeIntToMem(Expr _val, const PtrTy &ptr, MemValTy mem,
                                 unsigned byteSz, uint64_t align) {
  Expr val = _val;

  unsigned offsetBits = getByteAlignmentBits();
  bool wordAligned = offsetBits == 0 || align % wordSizeInBytes() == 0;
  if (!m_ignoreAlignment && !wordAligned) {
    return MemValTy(storeUnalignedIntToMem(val, ptr, mem, byteSz));
  }

  SmallVector<Expr, 16> words;
  if (byteSz == wordSizeInBytes()) {
    words.push_back(val);
  } else if (byteSz < wordSizeInBytes()) {
    val = m_ctx.alu().doZext(val, wordSizeInBits(), byteSz * 8);
    words.push_back(val);
  } else {
    for (unsigned i = 0; i < byteSz; i += wordSizeInBytes()) {
      unsigned lowBit = i * 8;
      Expr slice = m_ctx.alu().Extract({val, wordSizeInBits()}, lowBit,
                                       lowBit + wordSizeInBits() - 1);
      words.push_back(slice);
    }
  }

  MemValTy res = MemValTy(Expr());
  for (unsigned i = 0; i < words.size(); ++i) {
    res = m_memRepr->storeAlignedWordToMem(
        words[i], ptrAdd(ptr, i * wordSizeInBytes()), ptrSort(), mem);
    mem = res;
  }

  return res;
}

/// \brief stores integer into memory, address is not word aligned
///
/// \sa storeIntToMem
RawMemManagerCore::MemValTy
RawMemManagerCore::storeUnalignedIntToMem(const Expr &val, const PtrTy &ptr,
                                          MemValTy mem, unsigned byteSz) {
  unsigned offsetBits = getByteAlignmentBits();
  assert(offsetBits != 0);

  // for each byte (i) in val, load word w of i from memory, update one byte
  // of w, write back result
  MemValTy res = MemValTy(Expr());
  for (unsigned i = 0; i < byteSz; i++) {
    Expr wordAddress =
        m_ctx.alu().Extract({ptrAdd(ptr, i).toExpr(), ptrSizeInBits()},
                            offsetBits /* low */, ptrSizeInBits() - 1);
    Expr byteOffset =
        m_ctx.alu().Extract({ptrAdd(ptr, i).toExpr(), ptrSizeInBits()},
                            0 /* low */, offsetBits - 1);

    PtrTy alignedPtr = PtrTy(
        m_ctx.alu().Concat({wordAddress, ptrSizeInBits()} /* high */,
                           {bv::bvnum(0L, offsetBits, ptr.toExpr()->efac()),
                            offsetBits} /* low */));
    Expr existingWord = m_memRepr->loadAlignedWordFromMem(alignedPtr, mem);

    unsigned lowBit = i * 8;
    Expr byteToStore = m_ctx.alu().Extract({val, byteSz}, lowBit, lowBit + 7);

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
/// \param byteOffset symbolic expr indicating which byte to update
/// \return updated word
Expr RawMemManagerCore::setByteOfWord(Expr word, Expr byteData,
                                      Expr byteOffset) {
  // (x << 3) to get bit offset; zero extend to maintain word size
  // The byte offset within a word can be contained in log_2(wordSizeInBytes) +
  // 1 bits.
  byteOffset = m_ctx.alu().doZext(byteOffset, wordSizeInBits() - 3,
                                  llvm::Log2_64(wordSizeInBytes()) + 1);
  Expr bitOffset =
      m_ctx.alu().Concat({byteOffset, wordSizeInBits()} /* high */,
                         {bv::bvnum(0U, 3, byteOffset->efac()), 3} /* low */);

  // set a byte of existing word to 0
  Expr lowestByteMask = bv::bvnum(0xffU, wordSizeInBits(), word->efac());
  Expr addressByteMask = mk<BNOT>(mk<BSHL>(lowestByteMask, bitOffset));
  word = mk<BAND>(word, addressByteMask);

  // shift into position for zeroed part of existing word; mask and rewrite
  Expr shiftedByte =
      mk<BSHL>(m_ctx.alu().doZext(byteData, wordSizeInBits(), 8 /* one byte */),
               bitOffset);

  return mk<BOR>(word, shiftedByte);
}

/// \brief Stores a pointer into memory
/// \sa storeIntToMem
RawMemManagerCore::MemValTy RawMemManagerCore::storePtrToMem(const PtrTy &val,
                                                             const PtrTy ptr,
                                                             MemValTy mem,
                                                             unsigned byteSz,
                                                             uint64_t align) {
  // treat ptr as a a value
  return storeIntToMem(val.toExpr(), ptr, mem, byteSz, align);
}

/// \brief Returns an expression corresponding to a load from memory
///
/// \param[in] ptr is the pointer being dereferenced
/// \param[in] mem is the memory value being read from
/// \param[in] ty is the type of value being loaded
/// \param[in] align is the known alignment of the load
Expr RawMemManagerCore::loadValueFromMem(const PtrTy &ptr, const MemValTy &mem,
                                         const llvm::Type &ty, uint64_t align) {
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr.toExpr()->efac();

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
    res = loadPtrFromMem(ptr, mem, byteSz, align).toExpr();
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

RawMemManagerCore::MemValTy
RawMemManagerCore::storeValueToMem(Expr _val, PtrTy ptr, MemValTy mem,
                                   const llvm::Type &ty, uint32_t align) {
  assert(ptr.toExpr());
  Expr val = _val;
  const unsigned byteSz =
      m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
  ExprFactory &efac = ptr.toExpr()->efac();

  MemValTy res = MemValTy(Expr());
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
    res = storePtrToMem(PtrTy(val), ptr, mem, byteSz, align);
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
RawMemManagerCore::MemValTy RawMemManagerCore::MemSet(PtrTy ptr, Expr _val,
                                                      unsigned len,
                                                      MemValTy mem,
                                                      uint32_t align) {
  return m_memRepr->MemSet(ptr, _val, len, mem, wordSizeInBytes(), ptrSort(),
                           align);
}

/// \brief Executes symbolic memset with a symbolic length
RawMemManagerCore::MemValTy RawMemManagerCore::MemSet(PtrTy ptr, Expr _val,
                                                      Expr len, MemValTy mem,
                                                      uint32_t align) {
  return m_memRepr->MemSet(ptr, _val, len, mem, wordSizeInBytes(), ptrSort(),
                           align);
}

/// \brief Executes symbolic memcpy with concrete length
RawMemManagerCore::MemValTy RawMemManagerCore::MemCpy(PtrTy dPtr, PtrTy sPtr,
                                                      unsigned len,
                                                      MemValTy memTrsfrRead,
                                                      MemValTy memRead,
                                                      uint32_t align) {
  return m_memRepr->MemCpy(dPtr, sPtr, len, memTrsfrRead, memRead,
                           wordSizeInBytes(), ptrSort(), align);
}

RawMemManagerCore::MemValTy RawMemManagerCore::MemCpy(PtrTy dPtr, PtrTy sPtr,
                                                      Expr len,
                                                      MemValTy memTrsfrRead,
                                                      MemValTy memRead,
                                                      uint32_t align) {
  return m_memRepr->MemCpy(dPtr, sPtr, len, memTrsfrRead, memRead,
                           wordSizeInBytes(), ptrSort(), align);
}

/// \brief Executes symbolic memcpy from physical memory with concrete length
RawMemManagerCore::MemValTy RawMemManagerCore::MemFill(PtrTy dPtr, char *sPtr,
                                                       unsigned len,
                                                       MemValTy mem,
                                                       uint32_t align) {
  // same alignment behavior as galloc - default is word size of machine, can
  // only be increased
  return m_memRepr->MemFill(dPtr, sPtr, len, mem, wordSizeInBytes(), ptrSort(),
                            std::max(align, m_alignment));
}

/// \brief Executes inttoptr conversion
PtrTy RawMemManagerCore::inttoptr(Expr intVal, const Type &intTy,
                                  const Type &ptrTy) const {
  uint64_t intTySz = m_sem.sizeInBits(intTy);
  uint64_t ptrTySz = m_sem.sizeInBits(ptrTy);
  assert(ptrTySz == ptrSizeInBits());

  Expr res = intVal;
  if (ptrTySz > intTySz)
    res = m_ctx.alu().doZext(res, ptrTySz, intTySz);
  else if (ptrTySz < intTySz)
    res = m_ctx.alu().Extract({res, intTySz}, 0, ptrTySz - 1);
  return PtrTy(res);
}

Expr RawMemManagerCore::ptrUlt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUlt(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrUle(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUle(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrSlt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSlt(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrSle(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSle(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrUgt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUgt(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrUge(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doUge(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrSgt(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSgt(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrSge(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSge(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrEq(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doEq(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrNe(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doNe(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}
Expr RawMemManagerCore::ptrSub(PtrTy p1, PtrTy p2) const {
  return m_ctx.alu().doSub(p1.toExpr(), p2.toExpr(), ptrSizeInBits());
}

/// \brief Executes ptrtoint conversion
Expr RawMemManagerCore::ptrtoint(PtrTy ptr, const Type &ptrTy,
                                 const Type &intTy) const {
  uint64_t ptrTySz = m_sem.sizeInBits(ptrTy);
  uint64_t intTySz = m_sem.sizeInBits(intTy);
  assert(ptrTySz == ptrSizeInBits());

  Expr res = ptr.toExpr();
  if (ptrTySz < intTySz)
    res = m_ctx.alu().doZext(res, intTySz, ptrTySz);
  else if (ptrTySz > intTySz)
    res = m_ctx.alu().Extract({res, ptrTySz}, 0 /* low */, intTySz - 1);
  return res;
}

/// \brief Computes a pointer corresponding to the gep instruction
PtrTy RawMemManagerCore::gep(PtrTy ptr, gep_type_iterator it,
                             gep_type_iterator end) const {
  Expr offset = m_sem.symbolicIndexedOffset(it, end, m_ctx);
  return offset ? ptrAdd(ptr, offset) : PtrTy(Expr());
}

void RawMemManagerCore::onModuleEntry(const Module &M) {
  return m_allocator->onModuleEntry(M);
}

/// \brief Called when a function is entered for the first time
void RawMemManagerCore::onFunctionEntry(const Function &fn) {
  m_allocator->onFunctionEntry(fn);

  Expr res = m_sp0.toExpr();
  if (m_ctx.isKnownRegister(res))
    res = m_ctx.read(m_sp0.toExpr());

  // align of semantic_word_size, or 4 if it's less than 4
  unsigned offsetBits = 2;
  switch (wordSizeInBytes()) {
  case 8:
    offsetBits = 3;
  }
  m_ctx.addDef(bv::bvnum(0U, offsetBits, m_efac),
               m_ctx.alu().Extract({res, ptrSizeInBits()}, 0 /* low */,
                                   offsetBits - 1 /* high */));

  auto stackRange = m_allocator->getStackRange();

  // XXX Currently hard coded for typical 32bit system
  // -- 3GB upper limit
  m_ctx.addSide(ptrUle(
      PtrTy(res), PtrTy(m_ctx.alu().ui(stackRange.second, ptrSizeInBits()))));
  // -- 9MB stack
  m_ctx.addSide(ptrUge(
      PtrTy(res), PtrTy(m_ctx.alu().ui(stackRange.first, ptrSizeInBits()))));
}

RawMemManagerCore::MemValTy RawMemManagerCore::zeroedMemory() const {
  return MemValTy(
      m_memRepr->FilledMemory(ptrSort(), m_ctx.alu().ui(0, wordSizeInBits())));
}
OpSemAllocator &RawMemManagerCore::getMAllocator() const {
  return *m_allocator;
}
bool RawMemManagerCore::ignoreAlignment() const { return m_ignoreAlignment; }

PtrTy RawMemManagerCore::getAddressable(PtrTy p) { return p; }

// An empty destructor is needed because the class uses unique_ptr of
// forward declared types.
// See https://ortogonal.github.io/cpp/forward-declaration-and-smart-pointers/
RawMemManagerCore::~RawMemManagerCore() = default;
void RawMemManagerCore::dumpGlobalsMap() {
  return m_allocator->dumpGlobalsMap();
}
std::pair<char *, unsigned>
RawMemManagerCore::getGlobalVariableInitValue(const GlobalVariable &gv) {
  return m_allocator->getGlobalVariableInitValue(gv);
}

bool RawMemManagerCore::isPtrTyVal(Expr e) {
  return (e && !strct::isStructVal(e));
}

bool RawMemManagerCore::isMemVal(Expr e) {
  return (e && !strct::isStructVal(e));
}

} // namespace details
} // namespace seahorn
