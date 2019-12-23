#include "BvOpSem2Context.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {

class RawMemManager : public OpSemMemManager {
  /// \brief Allocates memory regions in virtual memory
  std::unique_ptr<OpSemAllocator> m_allocator;

  /// \brief Knows the memory representation and how to access it
  std::unique_ptr<OpSemMemRepr> m_memRepr;

  /// \brief Base name for non-deterministic pointer
  Expr m_freshPtrName;

  /// \brief Register that contains the value of the stack pointer on
  /// function entry
  Expr m_sp0;

  /// \brief Source of unique identifiers
  mutable unsigned m_id;

  /// \brief A null pointer expression (cache)
  Expr m_nullPtr;

public:
  RawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                unsigned wordSz, bool useLambdas = false);

  ~RawMemManager() override = default;

  /// Right now everything is an expression. In the future, we might have
  /// other types for PtrTy, such as a tuple of expressions
  using PtrTy = OpSemMemManager::PtrTy;

  PtrTy ptrSort() const override { return m_ctx.alu().intTy(ptrSzInBits()); }

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  PtrTy salloc(unsigned bytes, uint32_t align = 0);

  /// \brief Allocates memory on the stack and returns a pointer to it
  PtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0);

  /// \brief Returns a pointer value for a given stack allocation
  PtrTy mkStackPtr(unsigned offset);

  /// \brief Pointer to start of the heap
  PtrTy brk0Ptr();

  /// \brief Allocates memory on the heap and returns a pointer to it
  PtrTy halloc(unsigned _bytes, uint32_t align = 0);

  /// \brief Allocates memory on the heap and returns pointer to it
  PtrTy halloc(Expr bytes, uint32_t align = 0);

  /// \brief Allocates memory in global (data/bss) segment for given global
  PtrTy galloc(const GlobalVariable &gv, uint32_t align = 0);

  /// \brief Allocates memory in code segment for the code of a given function
  PtrTy falloc(const Function &fn);

  /// \brief Returns a function pointer value for a given function
  PtrTy getPtrToFunction(const Function &F);

  /// \brief Returns a pointer to a global variable
  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv);

  /// \brief Initialize memory used by the global variable
  void initGlobalVariable(const GlobalVariable &gv) const;

  /// \brief Creates a non-deterministic pointer that is aligned
  ///
  /// Top bits of the pointer are named by \p name and last \c log2(align)
  /// bits are set to zero
  PtrTy mkAlignedPtr(Expr name, uint32_t align) const;

  /// \brief Returns sort of a pointer register for an instruction
  Expr mkPtrRegisterSort(const Instruction &inst) const;

  /// \brief Returns sort of a pointer register for a function pointer
  Expr mkPtrRegisterSort(const Function &fn) const;

  /// \brief Returns sort of a pointer register for a global pointer
  Expr mkPtrRegisterSort(const GlobalVariable &gv) const { return ptrSort(); }

  /// \brief Returns sort of memory-holding register for an instruction
  Expr mkMemRegisterSort(const Instruction &inst) const;

  /// \brief Returns a fresh aligned pointer value
  PtrTy freshPtr();

  /// \brief Returns a null ptr
  PtrTy nullPtr() const;

  /// \brief Pointers have word address (high) and byte offset (low); returns
  /// number of bits for byte offset
  ///
  /// \return 0 if unsupported word size
  unsigned getByteAlignmentBits();

  /// \brief Fixes the type of a havoced value to mach the representation used
  /// by mem repr.
  ///
  /// \param reg
  /// \param val
  /// \return the coerced value.
  Expr coerce(Expr reg, Expr val);

  /// \brief Symbolic instructions to load a byte from memory, using word
  /// address and byte address
  ///
  /// \param[in] mem memory being accessed
  /// \param[in] address pointer being accessed, unaligned
  /// \param[in] offsetBits number of bits at end of pointers reserved for
  /// byte
  ///            address
  /// \return symbolic value of the byte at the specified address
  Expr extractUnalignedByte(Expr mem, PtrTy address, unsigned offsetBits);

  /// \brief Loads an integer of a given size from memory register
  ///
  /// \param[in] ptr pointer being accessed
  /// \param[in] memReg memory register into which \p ptr points
  /// \param[in] byteSz size of the integer in bytes
  /// \param[in] align known alignment of \p ptr
  /// \return symbolic value of the read integer
  Expr loadIntFromMem(PtrTy ptr, Expr memReg, unsigned byteSz, uint64_t align);

  /// \brief Loads a pointer stored in memory
  /// \sa loadIntFromMem
  PtrTy loadPtrFromMem(PtrTy ptr, Expr memReg, unsigned byteSz, uint64_t align);

  /// \brief Pointer addition with numeric offset
  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const;

  /// \brief Pointer addition with symbolic offset
  PtrTy ptrAdd(PtrTy ptr, Expr offset) const;

  /// \brief Stores an integer into memory
  ///
  /// Returns an expression describing the state of memory in \c memReadReg
  /// after the store
  /// \sa loadIntFromMem
  Expr storeIntToMem(Expr _val, PtrTy ptr, Expr memReadReg, unsigned byteSz,
                     uint64_t align);

  /// \brief stores integer into memory, address is not word aligned
  ///
  /// \sa storeIntToMem
  Expr storeUnalignedIntToMem(Expr val, PtrTy ptr, Expr mem, unsigned byteSz);

  /// \brief Given a word, updates a byte
  ///
  /// \param word existing word
  /// \param byteData updated byte
  /// \param byteOffset symbolic pointer indicating which byte to update
  /// \return updated word
  Expr setByteOfWord(Expr word, Expr byteData, PtrTy byteOffset);

  /// \brief Stores a pointer into memory
  /// \sa storeIntToMem
  Expr storePtrToMem(PtrTy val, PtrTy ptr, Expr memReadReg, unsigned byteSz,
                     uint64_t align);

  /// \brief Creates bit-vector of a given width filled with 0
  Expr mkZeroE(unsigned width, ExprFactory &efac) {
    return bv::bvnum(0UL, width, efac);
  }

  /// brief Creates a bit-vector for number 1 of a given width
  Expr mkOneE(unsigned width, ExprFactory &efac) {
    return bv::bvnum(1UL, width, efac);
  }

  /// \brief Returns an expression corresponding to a load from memory
  ///
  /// \param[in] ptr is the pointer being dereferenced
  /// \param[in] memReg is the memory register being read
  /// \param[in] ty is the type of value being loaded
  /// \param[in] align is the known alignment of the load
  Expr loadValueFromMem(PtrTy ptr, Expr memReg, const llvm::Type &ty,
                        uint64_t align);

  Expr storeValueToMem(Expr _val, PtrTy ptr, Expr memReadReg, Expr memWriteReg,
                       const llvm::Type &ty, uint32_t align);

  /// \brief Executes symbolic memset with a concrete length
  Expr MemSet(PtrTy ptr, Expr _val, unsigned len, Expr memReadReg,
              Expr memWriteReg, uint32_t align);

  /// \brief Executes symbolic memcpy with concrete length
  Expr MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, Expr memTrsfrReadReg,
              Expr memReadReg, Expr memWriteReg, uint32_t align);

  /// \brief Executes symbolic memcpy from physical memory with concrete
  /// length
  Expr MemFill(PtrTy dPtr, char *sPtr, unsigned len, uint32_t align = 0);

  /// \brief Executes inttoptr conversion
  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const;

  /// \brief Executes ptrtoint conversion
  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const;

  Expr ptrUlt(PtrTy p1, PtrTy p2) const;
  Expr ptrSlt(PtrTy p1, PtrTy p2) const;
  Expr ptrUle(PtrTy p1, PtrTy p2) const;
  Expr ptrSle(PtrTy p1, PtrTy p2) const;
  Expr ptrUgt(PtrTy p1, PtrTy p2) const;
  Expr ptrSgt(PtrTy p1, PtrTy p2) const;
  Expr ptrUge(PtrTy p1, PtrTy p2) const;
  Expr ptrSge(PtrTy p1, PtrTy p2) const;

  /// \brief Checks if two pointers are equal.
  Expr ptrEq(PtrTy p1, PtrTy p2) const;
  Expr ptrNe(PtrTy p1, PtrTy p2) const;

  Expr ptrSub(PtrTy p1, PtrTy p2) const;

  /// \brief Computes a pointer corresponding to the gep instruction
  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const;

  /// \brief Called when a function is entered for the first time
  void onFunctionEntry(const Function &fn);

  /// \brief Called when a module entered for the first time
  void onModuleEntry(const Module &M);

  /// \brief Debug helper
  void dumpGlobalsMap() { return m_allocator->dumpGlobalsMap(); }

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) {
    return m_allocator->getGlobalVariableInitValue(gv);
  }

  Expr zeroedMemory() const override; 

};
} // namespace details
} // namespace seahorn
