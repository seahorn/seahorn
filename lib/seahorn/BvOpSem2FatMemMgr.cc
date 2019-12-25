#include "BvOpSem2Context.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpStruct.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {

/// \brief provides Fat pointers and Fat memory to store them
class FatMemManager : public OpSemMemManager {
public:
  /// Right now everything is an expression. In the future, we might have
  /// other types for PtrTy, such as a tuple of expressions
  using PtrTy = OpSemMemManager::PtrTy;
  using FatPtrTy = OpSemMemManager::PtrTy;
  using RawPtrTy = OpSemMemManager::PtrTy;

  using MemValTy = OpSemMemManager::MemValTy;
  using FatMemValTy = OpSemMemManager::MemValTy;

private:
  /// \brief Memory manager for raw pointers
  RawMemManager m_mem;

  /// \brief A null pointer expression (cache)
  FatPtrTy m_nullPtr;

  /// \brief Converts a raw ptr to fat ptr with default value for fat
  FatPtrTy mkFatPtr(RawPtrTy rawPtr) const { return strct::mk(rawPtr); }
  /// \brief Update a given fat pointer with a raw address value
  FatPtrTy mkFatPtr(RawPtrTy rawPtr, FatPtrTy fat) const {
    if (fat->arity() == 1)
      return mkFatPtr(rawPtr);

    llvm::SmallVector<Expr, 8> kids;
    kids.push_back(rawPtr);
    for (unsigned i = 1, sz = fat->arity(); i < sz; ++i) {
      kids.push_back(fat->arg(i));
    }
    return strct::mk(kids);
  }
  /// \brief Extracts a raw pointer out of a fat pointer
  RawPtrTy mkRawPtr(FatPtrTy fatPtr) const {
    assert(strct::isStructVal(fatPtr));
    return strct::extractVal(fatPtr, 0);
  }

  /// \brief Extracts a raw memory value from a fat memory value
  MemValTy mkRawMem(FatMemValTy fatMem) const {
    assert(strct::isStructVal(fatMem));
    return strct::extractVal(fatMem, 0);
  }
  /// \brief Creates a fat memory value from raw memory with default value for
  /// fat
  FatMemValTy mkFatMem(MemValTy rawMem) const { return strct::mk(rawMem); }

public:
  FatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                unsigned wordSz, bool useLambdas = false);

  ~FatMemManager() override = default;

  FatPtrTy ptrSort() const override { return sort::structTy(m_mem.ptrSort()); }

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  FatPtrTy salloc(unsigned bytes, uint32_t align = 0) override {
    return mkFatPtr(m_mem.salloc(bytes, align));
  }

  /// \brief Allocates memory on the stack and returns a pointer to it
  FatPtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0) override {
    return mkFatPtr(m_mem.salloc(elmts, typeSz, align));
  }

  /// \brief Returns a pointer value for a given stack allocation
  FatPtrTy mkStackPtr(unsigned offset) override {
    return mkFatPtr(m_mem.mkStackPtr(offset));
  }

  /// \brief Pointer to start of the heap
  FatPtrTy brk0Ptr() override { return mkFatPtr(m_mem.brk0Ptr()); }

  /// \brief Allocates memory on the heap and returns a pointer to it
  FatPtrTy halloc(unsigned _bytes, uint32_t align = 0) override {
    return mkFatPtr(m_mem.halloc(_bytes, align));
  }

  /// \brief Allocates memory on the heap and returns pointer to it
  FatPtrTy halloc(Expr bytes, uint32_t align = 0) override {
    return mkFatPtr(m_mem.halloc(bytes, align));
  }

  /// \brief Allocates memory in global (data/bss) segment for given global
  FatPtrTy galloc(const GlobalVariable &gv, uint32_t align = 0) override {
    return mkFatPtr(m_mem.galloc(gv, align));
  }

  /// \brief Allocates memory in code segment for the code of a given
  /// function
  FatPtrTy falloc(const Function &fn) override {
    return mkFatPtr(m_mem.falloc(fn));
  }

  /// \brief Returns a function pointer value for a given function
  FatPtrTy getPtrToFunction(const Function &F) override {
    return mkFatPtr(m_mem.getPtrToFunction(F));
  }

  /// \brief Returns a pointer to a global variable
  FatPtrTy getPtrToGlobalVariable(const GlobalVariable &gv) override {
    return mkFatPtr(getPtrToGlobalVariable(gv));
  }

  /// \brief Initialize memory used by the global variable
  void initGlobalVariable(const GlobalVariable &gv) const {
    m_mem.initGlobalVariable(gv);
  }

  /// \brief Creates a non-deterministic pointer that is aligned
  ///
  /// Top bits of the pointer are named by \p name and last \c log2(align)
  /// bits are set to zero
  FatPtrTy mkAlignedPtr(Expr name, uint32_t align) const {
    return mkFatPtr(m_mem.mkAlignedPtr(name, align));
  }

  /// \brief Returns sort of a pointer register for an instruction
  Expr mkPtrRegisterSort(const Instruction &inst) const {
    return sort::structTy(m_mem.mkPtrRegisterSort(inst));
  }

  /// \brief Returns sort of a pointer register for a function pointer
  Expr mkPtrRegisterSort(const Function &fn) const { return ptrSort(); }

  /// \brief Returns sort of a pointer register for a global pointer
  Expr mkPtrRegisterSort(const GlobalVariable &gv) const { return ptrSort(); }

  /// \brief Returns sort of memory-holding register for an instruction
  Expr mkMemRegisterSort(const Instruction &inst) const {
    return sort::structTy(m_mem.mkMemRegisterSort(inst));
  }

  /// \brief Returns a fresh aligned pointer value
  FatPtrTy freshPtr() override { return mkFatPtr(m_mem.freshPtr()); }

  /// \brief Returns a null ptr
  FatPtrTy nullPtr() const override { return m_nullPtr; }

  /// \brief Fixes the type of a havoced value to mach the representation used
  /// by mem repr.
  ///
  /// \param sort
  /// \param val
  /// \return the coerced value.
  Expr coerce(Expr sort, Expr val) override {
    if (strct::isStructVal(val)) {
      // recursively coerce struct-ty
      llvm::SmallVector<Expr, 8> kids;
      assert(isOp<STRUCT_TY>(sort));
      assert(sort->arity() == val->arity());
      for (unsigned i = 0, sz = val->arity(); i < sz; ++i)
        kids.push_back(coerce(sort->arg(i), val->arg(i)));
      return strct::mk(kids);
    }

    return m_mem.coerce(sort, val);
  }

  /// \brief Loads an integer of a given size from memory register
  ///
  /// \param[in] ptr pointer being accessed
  /// \param[in] mem memory value into which \p ptr points
  /// \param[in] byteSz size of the integer in bytes
  /// \param[in] align known alignment of \p ptr
  /// \return symbolic value of the read integer
  Expr loadIntFromMem(FatPtrTy ptr, FatMemValTy mem, unsigned byteSz,
                      uint64_t align) override {
    return m_mem.loadIntFromMem(mkRawPtr(ptr), mkRawMem(mem), byteSz, align);
  }

  /// \brief Loads a pointer stored in memory
  /// \sa loadIntFromMem
  FatPtrTy loadPtrFromMem(FatPtrTy ptr, FatMemValTy mem, unsigned byteSz,
                          uint64_t align) override {
    return mkFatPtr(
        m_mem.loadPtrFromMem(mkRawPtr(ptr), mkRawMem(mem), byteSz, align));
  }

  /// \brief Pointer addition with numeric offset
  FatPtrTy ptrAdd(FatPtrTy ptr, int32_t _offset) const {
    PtrTy rawPtr = m_mem.ptrAdd(mkRawPtr(ptr), _offset);
    return mkFatPtr(rawPtr, ptr);
  }

  /// \brief Pointer addition with symbolic offset
  FatPtrTy ptrAdd(FatPtrTy ptr, Expr offset) const {
    PtrTy rawPtr = ptrAdd(mkRawPtr(ptr), offset);
    return mkFatPtr(rawPtr, ptr);
  }

  /// \brief Stores an integer into memory
  ///
  /// Returns an expression describing the state of memory in \c memReadReg
  /// after the store
  /// \sa loadIntFromMem
  FatMemValTy storeIntToMem(Expr _val, FatPtrTy ptr, FatMemValTy mem,
                            unsigned byteSz, uint64_t align) override {
    return mkFatMem(
        m_mem.storeIntToMem(_val, mkRawPtr(ptr), mkRawMem(mem), byteSz, align));
  }

  /// \brief Stores a pointer into memory
  /// \sa storeIntToMem
  FatMemValTy storePtrToMem(FatPtrTy val, FatPtrTy ptr, FatMemValTy mem,
                            unsigned byteSz, uint64_t align) override {
    return mkFatMem(m_mem.storePtrToMem(mkRawPtr(val), mkRawPtr(ptr),
                                        mkRawMem(mem), byteSz, align));
  }

  /// \brief Returns an expression corresponding to a load from memory
  ///
  /// \param[in] ptr is the pointer being dereferenced
  /// \param[in] memReg is the memory register being read
  /// \param[in] ty is the type of value being loaded
  /// \param[in] align is the known alignment of the load
  Expr loadValueFromMem(FatPtrTy ptr, FatMemValTy mem, const llvm::Type &ty,
                        uint64_t align) override {

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

  FatMemValTy storeValueToMem(Expr _val, FatPtrTy ptr, FatMemValTy mem,
                              const llvm::Type &ty, uint32_t align) override {
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
  FatMemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, FatMemValTy mem,
                     uint32_t align) override {
    return mkFatMem(
        m_mem.MemSet(mkRawPtr(ptr), _val, len, mkRawMem(mem), align));
  }

  /// \brief Executes symbolic memcpy with concrete length
  FatMemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, Expr memTrsfrRead,
                     uint32_t align) override {
    return mkFatMem(m_mem.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len,
                                 mkRawMem(memTrsfrRead), align));
  }

  /// \brief Executes symbolic memcpy from physical memory with concrete
  /// length
  FatMemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, FatMemValTy mem,
                      uint32_t align = 0) override {
    return mkFatMem(
        m_mem.MemFill(mkRawPtr(dPtr), sPtr, len, mkRawMem(mem), align));
  }

  /// \brief Executes inttoptr conversion
  FatPtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const {
    return mkFatPtr(m_mem.inttoptr(intVal, intTy, ptrTy));
  }

  /// \brief Executes ptrtoint conversion
  Expr ptrtoint(FatPtrTy ptr, const Type &ptrTy, const Type &intTy) const {
    return m_mem.ptrtoint(mkRawPtr(ptr), ptrTy, intTy);
  }

  Expr ptrUlt(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrUlt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSlt(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrSlt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrUle(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrUle(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSle(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrSle(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrUgt(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrUgt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSgt(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrSgt(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrUge(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrUge(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrSge(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrSge(mkRawPtr(p1), mkRawPtr(p2));
  }

  /// \brief Checks if two pointers are equal.
  Expr ptrEq(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrEq(mkRawPtr(p1), mkRawPtr(p2));
  }
  Expr ptrNe(FatPtrTy p1, FatPtrTy p2) const {
    return m_mem.ptrNe(mkRawPtr(p1), mkRawPtr(p2));
  }

  Expr ptrSub(FatPtrTy p1, FatPtrTy p2) const override {
    return m_mem.ptrSub(mkRawPtr(p1), mkRawPtr(p2));
  }

  /// \brief Computes a pointer corresponding to the gep instruction
  FatPtrTy gep(FatPtrTy ptr, gep_type_iterator it,
               gep_type_iterator end) const {
    PtrTy rawPtr = m_mem.gep(mkRawPtr(ptr), it, end);
    return mkFatPtr(rawPtr, ptr);
  }

  /// \brief Called when a function is entered for the first time
  void onFunctionEntry(const Function &fn) override {
    m_mem.onFunctionEntry(fn);
  }

  /// \brief Called when a module entered for the first time
  void onModuleEntry(const Module &M) override { m_mem.onModuleEntry(M); }

  /// \brief Debug helper
  void dumpGlobalsMap() override { m_mem.dumpGlobalsMap(); }

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) override {
    return m_mem.getGlobalVariableInitValue(gv);
  }

  FatMemValTy zeroedMemory() const override {
    return mkFatMem(m_mem.zeroedMemory());
  }
};

FatMemManager::FatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                             unsigned ptrSz, unsigned wordSz, bool useLambdas)
    : OpSemMemManager(sem, ctx, ptrSz, wordSz),
      m_mem(sem, ctx, ptrSz, wordSz, useLambdas) {

  m_nullPtr = mkFatPtr(m_mem.nullPtr());
}

OpSemMemManager *mkFatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas) {
  return new FatMemManager(sem, ctx, ptrSz, wordSz, useLambdas);
};

} // namespace details
} // namespace seahorn
