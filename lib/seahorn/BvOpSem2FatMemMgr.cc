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

private:
  /// \brief Memory manager for raw pointers
  RawMemManager m_mem;

  /// \brief A null pointer expression (cache)
  FatPtrTy m_nullPtr;

  FatPtrTy mkFatPtr(RawPtrTy rawPtr) const { return strct::mk(rawPtr); }
  RawPtrTy mkRawPtr(FatPtrTy fatPtr) const {
    assert(strct::isStructVal(fatPtr) || bind::isStructConst(fatPtr));

    if (strct::isStructVal(fatPtr))
      return strct::extractVal(fatPtr, 0);
    else /* structConst */ {
      // create a constant with the name |(extract-val fat-ptr 0)|
      // the name is unique
      assert(isOpX<FAPP>(fatPtr));
      Expr sort = bind::rangeTy(bind::fname(fatPtr))->arg(0);
      Expr name = strct::extractVal(fatPtr, 0);
      return bind::mkConst(name, sort);
    }
  }

public:
  FatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                unsigned wordSz, bool useLambdas = false);

  ~FatMemManager() override = default;

  FatPtrTy ptrSort() const override { return sort::structTy(m_mem.ptrSort()); }

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  FatPtrTy salloc(unsigned bytes, uint32_t align = 0) {
    return mkFatPtr(m_mem.salloc(bytes, align));
  }

  /// \brief Allocates memory on the stack and returns a pointer to it
  FatPtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0) {
    return mkFatPtr(m_mem.salloc(elmts, typeSz, align));
  }

  /// \brief Returns a pointer value for a given stack allocation
  FatPtrTy mkStackPtr(unsigned offset) {
    return mkFatPtr(m_mem.mkStackPtr(offset));
  }

  /// \brief Pointer to start of the heap
  FatPtrTy brk0Ptr() { return mkFatPtr(m_mem.brk0Ptr()); }

  /// \brief Allocates memory on the heap and returns a pointer to it
  FatPtrTy halloc(unsigned _bytes, uint32_t align = 0) {
    return mkFatPtr(m_mem.halloc(_bytes, align));
  }

  /// \brief Allocates memory on the heap and returns pointer to it
  FatPtrTy halloc(Expr bytes, uint32_t align = 0) {
    return mkFatPtr(m_mem.halloc(bytes, align));
  }

  /// \brief Allocates memory in global (data/bss) segment for given global
  FatPtrTy galloc(const GlobalVariable &gv, uint32_t align = 0) {
    return mkFatPtr(m_mem.galloc(gv, align));
  }

  /// \brief Allocates memory in code segment for the code of a given
  /// function
  FatPtrTy falloc(const Function &fn) { return mkFatPtr(m_mem.falloc(fn)); }

  /// \brief Returns a function pointer value for a given function
  FatPtrTy getPtrToFunction(const Function &F) {
    return mkFatPtr(m_mem.getPtrToFunction(F));
  }

  /// \brief Returns a pointer to a global variable
  FatPtrTy getPtrToGlobalVariable(const GlobalVariable &gv) {
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
    return m_mem.mkMemRegisterSort(inst);
  }

  /// \brief Returns a fresh aligned pointer value
  FatPtrTy freshPtr() { return mkFatPtr(m_mem.freshPtr()); }

  /// \brief Returns a null ptr
  FatPtrTy nullPtr() const { return m_nullPtr; }

  /// \brief Pointers have word address (high) and byte offset (low); returns
  /// number of bits for byte offset
  ///
  /// \return 0 if unsupported word size
  unsigned getByteAlignmentBits() { return m_mem.getByteAlignmentBits(); }

  /// \brief Fixes the type of a havoced value to mach the representation used
  /// by mem repr.
  ///
  /// \param reg
  /// \param val
  /// \return the coerced value.
  Expr coerce(Expr reg, Expr val) { return m_mem.coerce(reg, val); }

  /// \brief Symbolic instructions to load a byte from memory, using word
  /// address and byte address
  ///
  /// \param[in] mem memory being accessed
  /// \param[in] address pointer being accessed, unaligned
  /// \param[in] offsetBits number of bits at end of pointers reserved for
  /// byte
  ///            address
  /// \return symbolic value of the byte at the specified address
  Expr extractUnalignedByte(Expr mem, FatPtrTy address, unsigned offsetBits) {
    return m_mem.extractUnalignedByte(mem, mkRawPtr(address), offsetBits);
  }

  /// \brief Loads an integer of a given size from memory register
  ///
  /// \param[in] ptr pointer being accessed
  /// \param[in] memReg memory register into which \p ptr points
  /// \param[in] byteSz size of the integer in bytes
  /// \param[in] align known alignment of \p ptr
  /// \return symbolic value of the read integer
  Expr loadIntFromMem(FatPtrTy ptr, Expr memReg, unsigned byteSz,
                      uint64_t align) {
    return m_mem.loadIntFromMem(mkRawPtr(ptr), memReg, byteSz, align);
  }

  /// \brief Loads a pointer stored in memory
  /// \sa loadIntFromMem
  FatPtrTy loadPtrFromMem(FatPtrTy ptr, Expr memReg, unsigned byteSz,
                          uint64_t align) {
    return mkFatPtr(m_mem.loadPtrFromMem(mkRawPtr(ptr), memReg, byteSz, align));
  }

  /// \brief Pointer addition with numeric offset
  FatPtrTy ptrAdd(FatPtrTy ptr, int32_t _offset) const {
    return mkFatPtr(m_mem.ptrAdd(mkRawPtr(ptr), _offset));
  }

  /// \brief Pointer addition with symbolic offset
  FatPtrTy ptrAdd(PtrTy ptr, Expr offset) const {
    return mkFatPtr(ptrAdd(mkRawPtr(ptr), offset));
  }

  /// \brief Stores an integer into memory
  ///
  /// Returns an expression describing the state of memory in \c memReadReg
  /// after the store
  /// \sa loadIntFromMem
  Expr storeIntToMem(Expr _val, FatPtrTy ptr, Expr memReadReg, unsigned byteSz,
                     uint64_t align) {
    return m_mem.storeIntToMem(_val, mkRawPtr(ptr), memReadReg, byteSz, align);
  }

  /// \brief stores integer into memory, address is not word aligned
  ///
  /// \sa storeIntToMem
  Expr storeUnalignedIntToMem(Expr val, FatPtrTy ptr, Expr mem,
                              unsigned byteSz) {
    return m_mem.storeUnalignedIntToMem(val, mkRawPtr(ptr), mem, byteSz);
  }

  /// \brief Stores a pointer into memory
  /// \sa storeIntToMem
  Expr storePtrToMem(FatPtrTy val, FatPtrTy ptr, Expr memReadReg,
                     unsigned byteSz, uint64_t align) {
    return m_mem.storePtrToMem(mkRawPtr(val), mkRawPtr(ptr), memReadReg, byteSz,
                               align);
  }

  /// \brief Returns an expression corresponding to a load from memory
  ///
  /// \param[in] ptr is the pointer being dereferenced
  /// \param[in] memReg is the memory register being read
  /// \param[in] ty is the type of value being loaded
  /// \param[in] align is the known alignment of the load
  Expr loadValueFromMem(FatPtrTy ptr, Expr memReg, const llvm::Type &ty,
                        uint64_t align) {

    const unsigned byteSz =
        m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
    ExprFactory &efac = ptr->efac();

    Expr res;
    switch (ty.getTypeID()) {
    case Type::IntegerTyID:
      res = loadIntFromMem(ptr, memReg, byteSz, align);
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
      res = loadPtrFromMem(ptr, memReg, byteSz, align);
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

  Expr storeValueToMem(Expr _val, FatPtrTy ptr, Expr memReadReg,
                       Expr memWriteReg, const llvm::Type &ty, uint32_t align) {
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
      res = storeIntToMem(val, ptr, memReadReg, byteSz, align);
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
      res = storePtrToMem(val, ptr, memReadReg, byteSz, align);
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
    m_ctx.write(memWriteReg, res);
    return res;
  }

  /// \brief Executes symbolic memset with a concrete length
  Expr MemSet(PtrTy ptr, Expr _val, unsigned len, Expr memReadReg,
              Expr memWriteReg, uint32_t align) {
    return m_mem.MemSet(mkRawPtr(ptr), _val, len, memReadReg, memWriteReg,
                        align);
  }

  /// \brief Executes symbolic memcpy with concrete length
  Expr MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, Expr memTrsfrReadReg,
              Expr memReadReg, Expr memWriteReg, uint32_t align) {
    return m_mem.MemCpy(mkRawPtr(dPtr), mkRawPtr(sPtr), len, memTrsfrReadReg,
                        memReadReg, memWriteReg, align);
  }

  /// \brief Executes symbolic memcpy from physical memory with concrete
  /// length
  Expr MemFill(PtrTy dPtr, char *sPtr, unsigned len, uint32_t align = 0) {
    return m_mem.MemFill(mkRawPtr(dPtr), sPtr, len, align);
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
    return mkFatPtr(m_mem.gep(mkRawPtr(ptr), it, end));
  }

  /// \brief Called when a function is entered for the first time
  void onFunctionEntry(const Function &fn) { m_mem.onFunctionEntry(fn); }

  /// \brief Called when a module entered for the first time
  void onModuleEntry(const Module &M) { m_mem.onModuleEntry(M); }

  /// \brief Debug helper
  void dumpGlobalsMap() { m_mem.dumpGlobalsMap(); }

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) {
    return m_mem.getGlobalVariableInitValue(gv);
  }

  Expr zeroedMemory() const override {
    return m_mem.zeroedMemory();
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
