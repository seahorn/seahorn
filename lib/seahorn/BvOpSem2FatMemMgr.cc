#include "BvOpSem2Context.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "BvOpSem2MemManagerMixin.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpStruct.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {

static const unsigned int g_slotBitWidth = 64;
static const unsigned int g_slotByteWidth = g_slotBitWidth / 8;

static const unsigned int g_maxFatSlots = 2;
/// \brief provides Fat pointers and Fat memory to store them
class FatMemManager : public MemManagerCore {
public:
  /// PtrTy representation for this manager
  ///
  /// Currently internal representation is just an Expr
  struct PtrTyImpl {
    Expr m_v;
    PtrTyImpl(Expr &&e) : m_v(std::move(e)) {}
    PtrTyImpl(const Expr &e) : m_v(e) {}

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }
  };

  /// MemValTy representation for this manager
  ///
  /// Currently internal representation is just an Expr
  struct MemValTyImpl {
    Expr m_v;
    MemValTyImpl(Expr &&e) : m_v(std::move(e)) {}
    MemValTyImpl(const Expr &e) : m_v(e) {}

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }
    Expr getRaw() { return strct::extractVal(m_v, 0); }
  };

  using FatMemTag = MemoryFeatures::FatMem_tag;
  using TrackingTag = int;
  using WideMemTag = int;

  /// Right now everything is an expression. In the future, we might have
  /// other types for PtrTy, such as a tuple of expressions
  using BasePtrTy = OpSemMemManager::PtrTy;
  using RawPtrTy = OpSemMemManager::PtrTy;
  using BaseMemValTy = OpSemMemManager::MemValTy;

  using FatMemValTy = MemValTyImpl;
  using FatPtrTy = PtrTyImpl;

  using PtrTy = FatPtrTy;
  using MemValTy = FatMemValTy;
  using PtrSortTy = OpSemMemManager::PtrSortTy;
  using MemSortTy = OpSemMemManager::MemSortTy;
  using MemRegTy = OpSemMemManager::MemRegTy;

  // TODO: change all slot0,1 methods to return these types for easier reading
  using Slot0ValTy = Expr;
  using Slot1ValTy = Expr;

private:
  /// \brief Memory manager for raw pointers
  RawMemManager m_main;
  RawMemManager m_slot0;
  RawMemManager m_slot1;

  /// \brief A null pointer expression (cache)
  FatPtrTy m_nullPtr;

  /// \brief Converts a raw ptr to fat ptr with default value for fat
  FatPtrTy mkFatPtr(RawPtrTy rawPtr) const {
    return strct::mk(rawPtr, m_ctx.alu().ui(0, g_slotBitWidth),
                     m_ctx.alu().ui(1, g_slotBitWidth));
  }

  /// \brief Converts a raw ptr to fat ptr with default value for fat
  FatPtrTy mkFatPtr(RawPtrTy rawPtr, Slot0ValTy data0, Slot1ValTy data1) const {
    // TODO: check if data0 and data1 bitwidth is <= max or always guaranteed?
    return strct::mk(rawPtr, data0, data1);
  }

  /// \brief Update a given fat pointer with a raw address value
  FatPtrTy mkFatPtr(RawPtrTy rawPtr, FatPtrTy fat) const {
    if (fat.v()->arity() == 1)
      return mkFatPtr(rawPtr);

    llvm::SmallVector<Expr, 8> kids;
    kids.push_back(rawPtr);
    for (unsigned i = 1, sz = fat.v()->arity(); i < sz; ++i) {
      kids.push_back(fat.v()->arg(i));
    }
    return strct::mk(kids);
  }

  /// \brief Extracts a raw pointer out of a fat pointer
  RawPtrTy mkRawPtr(FatPtrTy fatPtr) const {
    assert(strct::isStructVal(fatPtr.v()));
    return strct::extractVal(fatPtr.v(), 0);
  }

  /// \brief Extracts a raw memory value from a fat memory value
  BaseMemValTy mkRawMem(FatMemValTy fatMem) const {
    assert(strct::isStructVal(fatMem.v()));
    return strct::extractVal(fatMem.v(), 0);
  }

  BaseMemValTy mkSlot0Mem(FatMemValTy fatMem) const {
    assert(strct::isStructVal(fatMem.v()));
    return strct::extractVal(fatMem.v(), 1);
  }

  BaseMemValTy mkSlot1Mem(FatMemValTy fatMem) const {
    assert(strct::isStructVal(fatMem.v()));
    return strct::extractVal(fatMem.v(), 2);
  }

  /// \brief Creates a fat memory value from raw memory with default value for
  /// fat
  FatMemValTy mkFatMem(BaseMemValTy rawMem, BaseMemValTy slot0Mem,
                       BaseMemValTy slot1Mem) const {
    return strct::mk(rawMem, slot0Mem, slot1Mem);
  }

public:
  FatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                unsigned wordSz, bool useLambdas = false);

  ~FatMemManager() = default;

  PtrSortTy ptrSort() const {
    return sort::structTy(m_main.ptrSort(), m_ctx.alu().intTy(g_slotBitWidth),
                          m_ctx.alu().intTy(g_slotBitWidth));
  }

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  FatPtrTy salloc(unsigned bytes, uint32_t align = 0) {
    auto e = m_main.salloc(bytes, align);
    m_slot0.salloc(bytes, align);
    m_slot1.salloc(bytes, align);
    return mkFatPtr(e);
  }

  /// \brief Allocates memory on the stack and returns a pointer to it
  FatPtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0) {
    auto e = m_main.salloc(elmts, typeSz, align);
    m_slot0.salloc(elmts, typeSz, align);
    m_slot1.salloc(elmts, typeSz, align);
    return mkFatPtr(e);
  }

  /// \brief Returns a pointer value for a given stack allocation
  FatPtrTy mkStackPtr(unsigned offset) {
    return mkFatPtr(m_main.mkStackPtr(offset));
  }

  /// \brief Pointer to start of the heap
  FatPtrTy brk0Ptr() { return mkFatPtr(m_main.brk0Ptr()); }

  /// \brief Allocates memory on the heap and returns a pointer to it
  FatPtrTy halloc(unsigned _bytes, uint32_t align = 0) {
    m_slot0.halloc(_bytes, align);
    m_slot1.halloc(_bytes, align);
    return mkFatPtr(m_main.halloc(_bytes, align));
  }

  /// \brief Allocates memory on the heap and returns pointer to it
  FatPtrTy halloc(Expr bytes, uint32_t align = 0) {
    m_slot0.halloc(bytes, align);
    m_slot1.halloc(bytes, align);
    return mkFatPtr(m_main.halloc(bytes, align));
  }

  /// \brief Allocates memory in global (data/bss) segment for given global
  FatPtrTy galloc(const GlobalVariable &gv, uint32_t align = 0) {
    m_slot0.galloc(gv, align);
    m_slot1.galloc(gv, align);
    return mkFatPtr(m_main.galloc(gv, align));
  }

  /// \brief Allocates memory in code segment for the code of a given
  /// function
  FatPtrTy falloc(const Function &fn) {
    m_slot0.falloc(fn);
    m_slot1.falloc(fn);
    return mkFatPtr(m_main.falloc(fn));
  }

  /// \brief Returns a function pointer value for a given function
  FatPtrTy getPtrToFunction(const Function &F) {
    m_slot0.getPtrToFunction(F);
    m_slot1.getPtrToFunction(F);
    return mkFatPtr(m_main.getPtrToFunction(F));
  }

  /// \brief Returns a pointer to a global variable
  FatPtrTy getPtrToGlobalVariable(const GlobalVariable &gv) {
    m_slot0.getPtrToGlobalVariable(gv);
    m_slot1.getPtrToGlobalVariable(gv);
    return mkFatPtr(m_main.getPtrToGlobalVariable(gv));
  }

  /// \brief Initialize memory used by the global variable
  void initGlobalVariable(const GlobalVariable &gv) const {
    m_main.initGlobalVariable(gv);
    m_slot0.initGlobalVariable(gv);
    m_slot1.initGlobalVariable(gv);
  }

  /// \brief Creates a non-deterministic pointer that is aligned
  ///
  /// Top bits of the pointer are named by \p name and last \c log2(align)
  /// bits are set to zero
  FatPtrTy mkAlignedPtr(Expr name, uint32_t align) const {
    m_slot0.mkAlignedPtr(name, align);
    m_slot1.mkAlignedPtr(name, align);
    return mkFatPtr(m_main.mkAlignedPtr(name, align));
  }

  /// \brief Returns sort of a pointer register for an instruction
  Expr mkPtrRegisterSort(const Instruction &inst) const {
    return sort::structTy(m_main.mkPtrRegisterSort(inst),
                          m_ctx.alu().intTy(g_slotBitWidth),
                          m_ctx.alu().intTy(g_slotBitWidth));
  }

  /// \brief Returns sort of a pointer register for a function pointer
  PtrSortTy mkPtrRegisterSort(const Function &fn) const { return ptrSort(); }

  /// \brief Returns sort of a pointer register for a global pointer
  Expr mkPtrRegisterSort(const GlobalVariable &gv) const { return ptrSort(); }

  /// \brief Returns sort of memory-holding register for an instruction
  Expr mkMemRegisterSort(const Instruction &inst) const {
    return sort::structTy(m_main.mkMemRegisterSort(inst),
                          m_slot0.mkMemRegisterSort(inst),
                          m_slot1.mkMemRegisterSort(inst));
  }

  /// \brief Returns a fresh aligned pointer value
  FatPtrTy freshPtr() { return mkFatPtr(m_main.freshPtr()); }

  /// \brief Returns a null ptr
  FatPtrTy nullPtr() const { return m_nullPtr; }

  /// \brief Fixes the type of a havoced value to mach the representation used
  /// by mem repr.
  ///
  /// \param sort
  /// \param val
  /// \return the coerced value.
  Expr coerce(Expr sort, Expr val) {
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

  /// \brief Loads an integer of a given size from 'raw' memory register
  ///
  /// \param[in] ptr pointer being accessed
  /// \param[in] mem memory value into which \p ptr points
  /// \param[in] byteSz size of the integer in bytes
  /// \param[in] align known alignment of \p ptr
  /// \return symbolic value of the read integer
  Expr loadIntFromMem(FatPtrTy ptr, FatMemValTy mem, unsigned byteSz,
                      uint64_t align) {
    return m_main.loadIntFromMem(mkRawPtr(ptr), mkRawMem(mem), byteSz, align);
  }

  /// \brief Loads a pointer stored in memory
  /// \sa loadIntFromMem
  FatPtrTy loadPtrFromMem(FatPtrTy ptr, FatMemValTy mem, unsigned byteSz,
                          uint64_t align) {
    BaseMemValTy rawVal =
        m_main.loadPtrFromMem(mkRawPtr(ptr), mkRawMem(mem), byteSz, align);
    BaseMemValTy slot0Val = m_slot0.loadIntFromMem(
        mkRawPtr(ptr), mkSlot0Mem(mem), g_slotByteWidth, align);
    BaseMemValTy slot1Val = m_slot1.loadIntFromMem(
        mkRawPtr(ptr), mkSlot1Mem(mem), g_slotByteWidth, align);
    return mkFatPtr(rawVal, slot0Val, slot1Val);
  }

  /// \brief Pointer addition with numeric offset
  FatPtrTy ptrAdd(FatPtrTy ptr, int32_t _offset) const {
    BasePtrTy rawPtr = m_main.ptrAdd(mkRawPtr(ptr), _offset);
    return mkFatPtr(rawPtr, ptr);
  }

  /// \brief Pointer addition with symbolic offset
  FatPtrTy ptrAdd(FatPtrTy ptr, Expr offset) const {
    BasePtrTy rawPtr = m_main.ptrAdd(mkRawPtr(ptr), offset);
    return mkFatPtr(rawPtr, ptr);
  }

  /// \brief Stores an integer into memory
  ///
  /// Returns an expression describing the state of memory in \c memReadReg
  /// after the store
  /// \sa loadIntFromMem
  FatMemValTy storeIntToMem(Expr _val, FatPtrTy ptr, FatMemValTy mem,
                            unsigned byteSz, uint64_t align) {
    return mkFatMem(
        m_main.storeIntToMem(_val, mkRawPtr(ptr), mkRawMem(mem), byteSz, align),
        mkSlot0Mem(mem), mkSlot1Mem(mem));
  }

  /// \brief Stores a pointer into memory
  /// \sa storeIntToMem
  FatMemValTy storePtrToMem(FatPtrTy val, FatPtrTy ptr, FatMemValTy mem,
                            unsigned byteSz, uint64_t align) {
    BaseMemValTy main = m_main.storePtrToMem(mkRawPtr(val), mkRawPtr(ptr),
                                             mkRawMem(mem), byteSz, align);
    BaseMemValTy slot0 =
        m_slot0.storeIntToMem(getFatData(val, 0), mkRawPtr(ptr),
                              mkSlot0Mem(mem), g_slotByteWidth, align);
    BaseMemValTy slot1 =
        m_slot1.storeIntToMem(getFatData(val, 1), mkRawPtr(ptr),
                              mkSlot1Mem(mem), g_slotByteWidth, align);
    auto res = mkFatMem(main, slot0, slot1);
    return res;
  }

  /// \brief Returns an expression corresponding to a load from memory
  ///
  /// \param[in] ptr is the pointer being dereferenced
  /// \param[in] memReg is the memory register being read
  /// \param[in] ty is the type of value being loaded
  /// \param[in] align is the known alignment of the load
  Expr loadValueFromMem(FatPtrTy ptr, FatMemValTy mem, const llvm::Type &ty,
                        uint64_t align) {

    const unsigned byteSz =
        m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
    ExprFactory &efac = ptr.v()->efac();

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

  FatMemValTy storeValueToMem(Expr _val, FatPtrTy ptr, FatMemValTy memIn,
                              const llvm::Type &ty, uint32_t align) {
    assert(ptr.v());
    Expr val = _val;
    const unsigned byteSz =
        m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
    ExprFactory &efac = ptr.v()->efac();

    FatMemValTy res(Expr(nullptr));
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
      report_fatal_error(out.str());
    }
    return res;
  }

  /// \brief Executes symbolic memset with a concrete length
  FatMemValTy MemSet(FatPtrTy ptr, Expr _val, unsigned len, FatMemValTy mem,
                     uint32_t align) {
    return mkFatMem(
        m_main.MemSet(mkRawPtr(ptr), _val, len, mkRawMem(mem), align),
        mkSlot0Mem(mem), mkSlot1Mem(mem));
  }

  FatMemValTy MemSet(FatPtrTy ptr, Expr _val, Expr len, FatMemValTy mem,
                     uint32_t align) {
    return mkFatMem(
        m_main.MemSet(mkRawPtr(ptr), _val, len, mkRawMem(mem), align),
        mkSlot0Mem(mem), mkSlot1Mem(mem));
  }

  /// \brief Executes symbolic memcpy with concrete length
  FatMemValTy MemCpy(FatPtrTy dPtr, FatPtrTy sPtr, unsigned len,
                     FatMemValTy memTrsfrRead, FatMemValTy memRead,
                     uint32_t align) {
    return mkFatMem(
        m_main.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len,
                      mkRawMem(memTrsfrRead), mkRawMem(memRead), align),
        m_slot0.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len,
                       mkSlot0Mem(memTrsfrRead), mkSlot0Mem(memRead), align),
        m_slot1.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len,
                       mkSlot1Mem(memTrsfrRead), mkSlot1Mem(memRead), align));
  }

  /// \brief Executes symbolic memcpy with concrete length
  FatMemValTy MemCpy(FatPtrTy dPtr, FatPtrTy sPtr, Expr len,
                     FatMemValTy memTrsfrRead, FatMemValTy memRead,
                     uint32_t align) {
    return mkFatMem(
        m_main.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len,
                      mkRawMem(memTrsfrRead), mkRawMem(memRead), align),
        m_slot0.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len,
                       mkSlot0Mem(memTrsfrRead), mkSlot0Mem(memRead), align),
        m_slot1.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len,
                       mkSlot1Mem(memTrsfrRead), mkSlot1Mem(memRead), align));
  }

  /// \brief Executes symbolic memcpy from physical memory with concrete
  /// length
  FatMemValTy MemFill(FatPtrTy dPtr, char *sPtr, unsigned len, FatMemValTy mem,
                      uint32_t align = 0) {
    return mkFatMem(
        m_main.MemFill(mkRawPtr(dPtr), sPtr, len, mkRawMem(mem), align),
        mkSlot0Mem(mem), mkSlot1Mem(mem));
  }

  /// \brief Executes inttoptr conversion
  FatPtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const {
    return mkFatPtr(m_main.inttoptr(intVal, intTy, ptrTy));
  }

  /// \brief Executes ptrtoint conversion. This only converts the raw ptr to
  /// int.
  Expr ptrtoint(FatPtrTy ptr, const Type &ptrTy, const Type &intTy) const {
    return m_main.ptrtoint(mkRawPtr(ptr), ptrTy, intTy);
  }

  Expr ptrUlt(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrUlt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSlt(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrSlt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrUle(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrUle(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSle(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrSle(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrUgt(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrUgt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSgt(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrSgt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrUge(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrUge(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSge(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrSge(mkRawPtr(p1), mkRawPtr(p2));
  }

  /// \brief Checks if two pointers are equal.
  Expr ptrEq(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrEq(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrNe(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrNe(mkRawPtr(p1), mkRawPtr(p2));
  }

  Expr ptrSub(FatPtrTy p1, FatPtrTy p2) const {
    return m_main.ptrSub(mkRawPtr(p1), mkRawPtr(p2));
  }

  /// \brief Computes a pointer corresponding to the gep instruction
  FatPtrTy gep(FatPtrTy ptr, gep_type_iterator it,
               gep_type_iterator end) const {
    // Here the resultant pointer automatically gets the same slot(s) data
    // as the original. Therefore we don't require the client to manually
    // update slot(s) data after a gep call.
    BasePtrTy rawPtr = m_main.gep(mkRawPtr(ptr), it, end);
    return mkFatPtr(rawPtr, ptr);
  }

  /// \brief Called when a function is entered for the first time
  void onFunctionEntry(const Function &fn) {
    m_main.onFunctionEntry(fn);
    m_slot0.onFunctionEntry(fn);
    m_slot1.onFunctionEntry(fn);
  }

  /// \brief Called when a module entered for the first time
  void onModuleEntry(const Module &M) {
    m_main.onModuleEntry(M);
    m_slot0.onModuleEntry(M);
    m_slot1.onModuleEntry(M);
  }

  /// \brief Debug helper
  void dumpGlobalsMap() { m_main.dumpGlobalsMap(); }

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) {
    // TODO: do we need to make a union
    return m_main.getGlobalVariableInitValue(gv);
  }

  FatMemValTy zeroedMemory() const {
    return mkFatMem(m_main.zeroedMemory(), m_slot0.zeroedMemory(),
                    m_slot1.zeroedMemory());
  }

  Expr getFatData(FatPtrTy p, unsigned SlotIdx) {
    assert(strct::isStructVal(p.v()));
    assert(SlotIdx < g_maxFatSlots);
    return strct::extractVal(p.v(), 1 + SlotIdx);
  }

  FatPtrTy setFatData(FatPtrTy p, unsigned SlotIdx, Expr data) {
    assert(strct::isStructVal(p.v()));
    assert(SlotIdx < g_maxFatSlots);
    return strct::insertVal(p.v(), 1 + SlotIdx, data);
  }

  RawPtrTy getAddressable(FatPtrTy p) const { return mkRawPtr(p); }

  bool isPtrTyVal(Expr e) const {
    // struct with raw ptr + fat slots
    return e && strct::isStructVal(e) && e->arity() == (1 + g_maxFatSlots);
  }

  bool isMemVal(Expr e) const {
    // struct with raw ptr + fat slots
    return e && strct::isStructVal(e) && e->arity() == (1 + g_maxFatSlots);
  }
};

FatMemManager::FatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                             unsigned ptrSz, unsigned wordSz, bool useLambdas)
    : MemManagerCore(sem, ctx, ptrSz, wordSz,
                     false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_nullPtr(mkFatPtr(m_main.nullPtr())),
      m_slot0(sem, ctx, ptrSz, g_slotByteWidth, useLambdas),
      m_slot1(sem, ctx, ptrSz, g_slotByteWidth, useLambdas) {}

OpSemMemManager *mkFatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas) {
  return new OpSemMemManagerMixin<FatMemManager>(sem, ctx, ptrSz, wordSz,
                                                 useLambdas);
}
} // namespace details
} // namespace seahorn
