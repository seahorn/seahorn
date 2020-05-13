#pragma once

#include "seahorn/BvOpSem2.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/Smt/EZ3.hh"

namespace seahorn {
namespace details {

class OpSemAlu;
class OpSemMemManager;
class OpSemMemRepr;
class OpSemVisitorBase;

/// \brief Operational Semantics Context, a.k.a. Semantic Machine
/// Keeps track of the state of the current semantic machine and provides
/// API to manipulate the machine.
class Bv2OpSemContext : public OpSemContext {
  friend class OpSemVisitorBase;

private:
  /// \brief Set memory manager to be used by the machine
  void setMemManager(OpSemMemManager *man);

  /// \brief Reference to parent operational semantics
  Bv2OpSem &m_sem;

  /// \brief currently executing function
  const Function *m_func;

  /// \brief Currently executing basic block
  const BasicBlock *m_bb;

  /// \brief Current instruction to be executed
  BasicBlock::const_iterator m_inst;

  /// \brief Previous basic block (or null if not known)
  const BasicBlock *m_prev;

  /// \brief Meta register that contains the name of the register to be
  /// used in next memory load
  Expr m_readRegister;

  /// \brief Meta register that contains the name of the register to be
  /// used in next memory store
  Expr m_writeRegister;

  /// \brief Indicates whether the current in/out memory is a unique scalar
  /// memory cell. A unique scalar memory cell is a memory cell that contains a
  /// scalar and is never aliased.
  bool m_scalar;

  /// \brief An additional memory read register that is used in memory transfer
  /// instructions that read/write from multiple memory regions
  Expr m_trfrReadReg;

  /// \brief Argument stack for the current function call
  ExprVector m_fparams;

  /// \brief Instructions that were treated as a noop by the machine
  DenseSet<const Instruction *> m_ignored;

  using FlatExprSet = boost::container::flat_set<Expr>;

  /// \brief Declared symbolic registers
  FlatExprSet m_registers;

  using ValueExprMap = DenseMap<const llvm::Value *, Expr>;

  // \brief Map from \c llvm::Value to a registers
  ValueExprMap m_valueToRegister;

  using OpSemMemManagerPtr = std::unique_ptr<OpSemMemManager>;

  /// \brief Memory manager for the machine
  OpSemMemManagerPtr m_memManager;

  using OpSemAluPtr = std::unique_ptr<OpSemAlu>;

  /// \brief ALU for basic instructions
  OpSemAluPtr m_alu;
  /// \brief Pointer to the parent a parent context
  ///
  /// If not null, then the current context is a fork of the parent context
  /// Otherwise, the current context is the main context
  const Bv2OpSemContext *m_parent = nullptr;

  /// Cache for helper expressions. Avoids creating them on the fly.

  /// \brief Numeric zero
  Expr zeroE;
  /// \brief Numeric one
  Expr oneE;

  /// \brief local simplifier
  std::shared_ptr<EZ3> m_z3;
  std::shared_ptr<ZSimplifier<EZ3>> m_z3_simplifier;

public:
  /// \brief Create a new context with given semantics, values, and side
  Bv2OpSemContext(Bv2OpSem &sem, SymStore &values, ExprVector &side);
  /// \brief Clone a context with possibly new values and side condition
  /// \sa Bv2OpSem::fork
  Bv2OpSemContext(SymStore &values, ExprVector &side,
                  const Bv2OpSemContext &other);
  Bv2OpSemContext(const Bv2OpSemContext &) = delete;
  ~Bv2OpSemContext() override = default;

  EZ3 *getZ3() const { return m_z3.get(); }

  /// \brief Writes value \p u into symbolic register \p v
  void write(Expr v, Expr u);
  /// \brief Returns size of a memory word
  unsigned wordSzInBytes() const;
  /// \brief Returns size in bits of a memory word
  unsigned wordSzInBits() const { return wordSzInBytes() * 8; }
  /// \brief Returns size of a pointer in bits
  unsigned ptrSzInBits() const;

  /// \brief Returns the memory manager
  OpSemMemManager *getMemManager() const { return m_memManager.get(); }
  OpSemMemManager &mem() const {
    assert(!m_parent || !m_memManager);
    if (m_memManager)
      return *m_memManager;
    if (m_parent)
      return m_parent->mem();
  }

  OpSemAlu &alu() const {
    if (m_alu)
      return *m_alu;
    if (m_parent)
      return m_parent->alu();
    llvm_unreachable(nullptr);
  }

  /// \brief Push parameter on a stack for a function call
  void pushParameter(Expr v) { m_fparams.push_back(v); }
  /// \brief Update the value of \p idx parameter on the stack
  void setParameter(unsigned idx, Expr v) { m_fparams[idx] = v; }
  /// \brief Reset all parameters
  void resetParameters() { m_fparams.clear(); }
  /// \brief Return the current parameter stack as a vector
  const ExprVector &getParameters() const { return m_fparams; }

  /// \brief Return the currently executing basic block
  const BasicBlock *getCurrBb() const { return m_bb; }
  /// \brief Set the previously executed basic block
  void setPrevBb(const BasicBlock &prev) { m_prev = &prev; }

  /// \brief Return basic block executed prior to the current one (used to
  /// resolve PHI instructions)
  const BasicBlock *getPrevBb() const { return m_prev; }
  /// \brief Currently executed instruction
  const Instruction &getCurrentInst() const { return *m_inst; }
  /// \brief Set instruction to be executed next
  void setInstruction(const Instruction &inst) {
    m_inst = BasicBlock::const_iterator(&inst);
  }
  /// \brief True if executing the last instruction in the current basic block
  bool isAtBbEnd() const { return m_inst == m_bb->end(); }
  /// \brief Move to next instructions in the basic block to execute
  Bv2OpSemContext &operator++() {
    ++m_inst;
    return *this;
  }

  void setMemReadRegister(Expr r) { m_readRegister = r; }
  Expr getMemReadRegister() { return m_readRegister; }
  void setMemWriteRegister(Expr r) { m_writeRegister = r; }
  Expr getMemWriteRegister() { return m_writeRegister; }
  bool isMemScalar() { return m_scalar; }
  void setMemScalar(bool v) { m_scalar = v; }

  void setMemTrsfrReadReg(Expr r) { m_trfrReadReg = r; }
  Expr getMemTrsfrReadReg() { return m_trfrReadReg; }

  /// \brief Load value of type \p ty with alignment \align pointed by the
  /// symbolic pointer \ptr. Memory register being read from must be set via
  /// \f setMemReadRegister
  Expr loadValueFromMem(Expr ptr, const llvm::Type &ty, uint32_t align);

  /// \brief Store a value \val to symbolic memory at address \p ptr
  ///
  /// Read and write memory registers must be set with setMemReadRegister and
  /// setMemWriteRegister prior to this operation.
  Expr storeValueToMem(Expr val, Expr ptr, const llvm::Type &ty,
                       uint32_t align);

  /// \brief Perform symbolic memset
  Expr MemSet(Expr ptr, Expr val, unsigned len, uint32_t align);

  /// \brief Perform symbolic memcpy
  Expr MemCpy(Expr dPtr, Expr sPtr, unsigned len, uint32_t align);

  /// \brief Copy concrete memory into symbolic memory
  Expr MemFill(Expr dPtr, char *sPtr, unsigned len, uint32_t align = 0);

  /// \brief Execute inttoptr
  Expr inttoptr(Expr intValue, const Type &intTy, const Type &ptrTy) const;
  /// \brief Execute ptrtoint
  Expr ptrtoint(Expr ptrValue, const Type &ptrTy, const Type &intTy) const;
  /// \brief Execute gep
  Expr gep(Expr ptr, gep_type_iterator it, gep_type_iterator end) const;

  /// \brief Called when a module is entered
  void onModuleEntry(const Module &M) override;
  /// \brief Called when a function is entered
  void onFunctionEntry(const Function &fn) override;
  /// \brief Called when a function returns
  void onFunctionExit(const Function &fn) override {}

  /// \brief Call when a basic block is entered
  void onBasicBlockEntry(const BasicBlock &bb) override;

  /// \brief declare \p v as a new register for the machine
  void declareRegister(Expr v);
  /// \brief Returns true if \p is a known register
  bool isKnownRegister(Expr v);

  /// \brief Create a register of the correct sort to hold the value returned by
  /// the instruction
  Expr mkRegister(const llvm::Instruction &inst);
  /// \brief Create a register to hold control information of a basic block
  Expr mkRegister(const llvm::BasicBlock &bb);
  /// \brief Create a register to hold a pointer to a global variable
  Expr mkRegister(const llvm::GlobalVariable &gv);
  /// \brief Create a register to hold a pointer to a function
  Expr mkRegister(const llvm::Function &fn);
  /// \brief Create a register to hold a value
  Expr mkRegister(const llvm::Value &v);
  /// \brief Return a register that contains \p v, if it exists
  Expr getRegister(const llvm::Value &v) const {
    Expr res = m_valueToRegister.lookup(&v);
    if (!res && m_parent)
      res = m_parent->getRegister(v);
    return res;
  }

  /// \brief Return sort for a function pointer
  Expr mkPtrRegisterSort(const Function &fn) const;
  /// \brief Return a sort for a pointer to global variable register
  Expr mkPtrRegisterSort(const GlobalVariable &gv) const;
  /// \brief Return a sort for a pointer
  Expr mkPtrRegisterSort(const Instruction &inst) const;
  /// \brief Return a sort for a memory register
  Expr mkMemRegisterSort(const Instruction &inst) const;

  /// \brief Returns symbolic value of a constant expression \p c
  Expr getConstantValue(const llvm::Constant &c);

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv);

  /// \brief Return true if \p inst is ignored by the semantics
  bool isIgnored(const Instruction &inst) const {
    return m_ignored.count(&inst);
  }

  // \brief Mark \p inst to be ignored
  void ignore(const Instruction &inst) { m_ignored.insert(&inst); }

  /// \brief Fork current context and update new copy with a given store and
  /// side condition
  OpSemContextPtr fork(SymStore &values, ExprVector &side) {
    return OpSemContextPtr(new Bv2OpSemContext(values, side, *this));
  }

private:
  static Bv2OpSemContext &ctx(OpSemContext &ctx) {
    return static_cast<Bv2OpSemContext &>(ctx);
  }
};

/// \brief ALU for basic arithmetic and logic operations
class OpSemAlu {
protected:
  Bv2OpSemContext &m_ctx;

public:
  OpSemAlu(Bv2OpSemContext &ctx);
  virtual ~OpSemAlu() = default;

  Bv2OpSemContext &ctx() const { return m_ctx; }
  ExprFactory &efac() const { return m_ctx.efac(); }

  // coerce between bv1 and bool.
  // XXX: These should be hidden inside ALU implementation
  // XXX: Should not be exposed to clients
  virtual Expr boolToBv1(Expr e) = 0;
  virtual Expr bv1ToBool(Expr e) = 0;

  /// \brief Integer type of a given bit width on the ALU
  virtual Expr intTy(unsigned bitWidth) = 0;
  /// \brief Boolean type of the ALU
  virtual Expr boolTy() = 0;

  virtual bool isNum(Expr v) = 0;
  virtual expr::mpz_class toNum(Expr v) = 0;
  virtual Expr si(expr::mpz_class k, unsigned bitWidth) = 0;
  virtual Expr doAdd(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doSub(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doMul(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doUDiv(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doSDiv(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doURem(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doSRem(Expr op0, Expr op1, unsigned bitWidth) = 0;

  virtual Expr doAnd(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doOr(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doXor(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doNot(Expr op0, unsigned bitWidth) = 0;

  virtual Expr doEq(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doNe(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doUlt(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doSlt(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doUgt(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doSgt(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doUle(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doSle(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doUge(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr doSge(Expr op0, Expr op1, unsigned bitWidth) = 0;

  virtual Expr doTrunc(Expr op, unsigned bitWidth) = 0;
  virtual Expr doZext(Expr op, unsigned bitWidth, unsigned opBitWidth) = 0;
  virtual Expr doSext(Expr op, unsigned bitWidth, unsigned opBitWidth) = 0;
  virtual Expr Extract(std::pair<Expr, unsigned int> op, unsigned begin,
                       unsigned end) = 0;
  virtual Expr Concat(std::pair<Expr, unsigned int> opHigh,
                      std::pair<Expr, unsigned int> opLow) = 0;

  // Arithmetic intrinsics with overflow
  virtual Expr IsSaddNoOverflow(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr IsBaddNoUnderflow(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr IsUaddNoOverflow(Expr op0, Expr op1, unsigned bitWidth) = 0;

  virtual Expr IsBsubNoOverflow(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr IsSsubNoUnderflow(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr IsUsubNoUnderflow(Expr op0, Expr op1, unsigned bitWidth) = 0;

  virtual Expr IsSmulNoOverflow(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr IsUmulNoOverflow(Expr op0, Expr op1, unsigned bitWidth) = 0;
  virtual Expr IsBmulNoUnderflow(Expr op0, Expr op1, unsigned bitWidth) = 0;
};

std::unique_ptr<OpSemAlu> mkBvOpSemAlu(Bv2OpSemContext &ctx);

/// \brief  Lays out / allocates pointers in a virtual memory space
///
/// The class is responsible for laying out allocated object in memory.
/// The exact semantics are yet to be determined. Currently, it is assumed
/// that the layout respects stack / heap / text area separation.
///
/// Note that in addition to the parameters passed directly, the allocator has
/// access to the \p OpSemContext so it can depend on the current instruction
/// being executed.
class OpSemAllocator {
protected:
  struct AllocInfo;
  struct FuncAllocInfo;
  struct GlobalAllocInfo;

  OpSemMemManager &m_mem;
  Bv2OpSemContext &m_ctx;
  Bv2OpSem &m_sem;
  ExprFactory &m_efac;

  /// \brief All known stack allocations
  std::vector<AllocInfo> m_allocas;
  /// \brief All known code allocations
  std::vector<FuncAllocInfo> m_funcs;
  /// \brief All known global allocations
  std::vector<GlobalAllocInfo> m_globals;

  // TODO: turn into user-controlled parameters
  unsigned MAX_STACK_ADDR = 0xC0000000;
  unsigned MIN_STACK_ADDR = (MAX_STACK_ADDR - 9437184);
  unsigned TEXT_SEGMENT_START = 0x08048000;

public:
  using AddrInterval = std::pair<unsigned, unsigned>;
  OpSemAllocator(OpSemMemManager &mem);

  virtual ~OpSemAllocator();

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  virtual AddrInterval salloc(unsigned bytes, uint32_t align) = 0;

  /// \brief Allocates memory on the stack
  ///
  /// \param bytes is a symbolic representation for number of bytes to allocate
  virtual AddrInterval salloc(Expr bytes, uint32_t align) = 0;

  /// \brief Address at which heap starts (initial value of \c brk)
  unsigned brk0Addr();

  bool isBadAddrInterval(AddrInterval range) {
    return range == AddrInterval(0, 0);
  }

  /// \brief Return the maximal legal range of the stack pointer
  AddrInterval getStackRange() { return {MIN_STACK_ADDR, MAX_STACK_ADDR}; }

  /// \brief Called whenever a new module is to be executed
  virtual void onModuleEntry(const Module &M) {}

  /// \brief Called whenever a new function is to be executed
  virtual void onFunctionEntry(const Function &fn) {}

  /// \brief Allocates memory on the heap and returns a pointer to it
  virtual AddrInterval halloc(unsigned _bytes, unsigned align) {
    llvm_unreachable("not implemented");
  }

  /// \brief Allocates memory in global (data/bss) segment for given global
  /// \param bytes is the expected size of allocation
  virtual AddrInterval galloc(const GlobalVariable &gv, uint64_t bytes,
                              unsigned align);

  /// \brief Allocates memory in code segment for the code of a given function
  virtual AddrInterval falloc(const Function &fn, unsigned align);

  /// \brief Returns an address at which a given function resides
  virtual unsigned getFunctionAddr(const Function &F, unsigned align);

  /// \brief Returns an address of a global variable
  virtual unsigned getGlobalVariableAddr(const GlobalVariable &gv,
                                         unsigned bytes, unsigned align);

  /// \brief Returns an address of memory segment to store value of the variable
  virtual char *getGlobalVariableMem(const GlobalVariable &gv) const;

  /// \brief Returns initial value of a global variable
  ///
  /// Returns (nullptr, 0) if the global variable has no known initial value
  virtual std::pair<char *, unsigned>
  getGlobalVariableInitValue(const GlobalVariable &gv);

  virtual void dumpGlobalsMap();
};

/// \brief Creates an instance of OpSemAllocator
std::unique_ptr<OpSemAllocator> mkNormalOpSemAllocator(OpSemMemManager &mem);
std::unique_ptr<OpSemAllocator> mkStaticOpSemAllocator(OpSemMemManager &mem);

/// \brief Memory manager for OpSem machine
class OpSemMemManager {
public:
  /// \brief type for pointers
  /// Currently all expressions are of opaque type Expr. The extra type
  /// annotations are to communicate intend only.
  using PtrTy = Expr;
  using MemRegTy = Expr;
  using MemValTy = Expr;

protected:
  /// \brief Parent Operational Semantics
  Bv2OpSem &m_sem;
  /// \brief Parent Semantics Context
  Bv2OpSemContext &m_ctx;
  /// \brief Parent expression factory
  ExprFactory &m_efac;

  /// \brief Ptr size in bytes
  uint32_t m_ptrSz;
  /// \brief Word size in bytes
  uint32_t m_wordSz;
  /// \brief Preferred alignment in bytes
  ///
  /// Must be divisible by \t m_wordSz
  uint32_t m_alignment;

public:
  OpSemMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                  unsigned wordSz);

  virtual ~OpSemMemManager() = default;

  Bv2OpSem &sem() const { return m_sem; }
  Bv2OpSemContext &ctx() const { return m_ctx; }

  unsigned ptrSzInBits() const { return m_ptrSz * 8; }
  unsigned wordSzInBytes() const { return m_wordSz; }
  unsigned wordSzInBits() const { return m_wordSz * 8; }

  virtual PtrTy ptrSort() const = 0;

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  virtual PtrTy salloc(unsigned bytes, uint32_t align = 0) = 0;

  /// \brief Allocates memory on the stack and returns a pointer to it
  virtual PtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align = 0) = 0;

  /// \brief Returns a pointer value for a given stack allocation
  virtual PtrTy mkStackPtr(unsigned offset) = 0;

  /// \brief Pointer to start of the heap
  virtual PtrTy brk0Ptr() = 0;

  /// \brief Allocates memory on the heap and returns a pointer to it
  virtual PtrTy halloc(unsigned _bytes, uint32_t align = 0) = 0;

  /// \brief Allocates memory on the heap and returns pointer to it
  virtual PtrTy halloc(Expr bytes, uint32_t align = 0) = 0;

  /// \brief Allocates memory in global (data/bss) segment for given global
  virtual PtrTy galloc(const GlobalVariable &gv, uint32_t align = 0) = 0;

  /// \brief Allocates memory in code segment for the code of a given function
  virtual PtrTy falloc(const Function &fn) = 0;

  /// \brief Returns a function pointer value for a given function
  virtual PtrTy getPtrToFunction(const Function &F) = 0;

  /// \brief Returns a pointer to a global variable
  virtual PtrTy getPtrToGlobalVariable(const GlobalVariable &gv) = 0;

  /// \brief Initialize memory used by the global variable
  virtual void initGlobalVariable(const GlobalVariable &gv) const = 0;

  /// \brief Creates a non-deterministic pointer that is aligned
  ///
  /// Top bits of the pointer are named by \p name and last \c log2(align) bits
  /// are set to zero
  virtual PtrTy mkAlignedPtr(Expr name, uint32_t align) const = 0;

  /// \brief Returns sort of a pointer register for an instruction
  virtual Expr mkPtrRegisterSort(const Instruction &inst) const = 0;

  /// \brief Returns sort of a pointer register for a function pointer
  virtual Expr mkPtrRegisterSort(const Function &fn) const = 0;

  /// \brief Returns sort of a pointer register for a global pointer
  virtual Expr mkPtrRegisterSort(const GlobalVariable &gv) const = 0;

  /// \brief Returns sort of memory-holding register for an instruction
  virtual Expr mkMemRegisterSort(const Instruction &inst) const = 0;

  /// \brief Returns a fresh aligned pointer value
  virtual PtrTy freshPtr() = 0;

  /// \brief Returns a null ptr
  virtual PtrTy nullPtr() const = 0;

  /// \brief Fixes the type of a havoced value to mach the representation used
  /// by mem repr.
  ///
  /// \param sort
  /// \param val
  /// \return the coerced value.
  virtual Expr coerce(Expr sort, Expr val) = 0;

  /// \brief Pointer addition with numeric offset
  virtual PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const = 0;

  /// \brief Pointer addition with symbolic offset
  virtual PtrTy ptrAdd(PtrTy ptr, Expr offset) const = 0;

  /// \brief Loads an integer of a given size from memory register
  ///
  /// \param[in] ptr pointer being accessed
  /// \param[in] memReg memory register into which \p ptr points
  /// \param[in] byteSz size of the integer in bytes
  /// \param[in] align known alignment of \p ptr
  /// \return symbolic value of the read integer
  virtual Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                              uint64_t align) = 0;

  /// \brief Loads a pointer stored in memory
  /// \sa loadIntFromMem
  virtual PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                               uint64_t align) = 0;

  /// \brief Stores an integer into memory
  ///
  /// Returns an expression describing the state of memory in \c memReadReg
  /// after the store
  /// \sa loadIntFromMem
  virtual Expr storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                             unsigned byteSz, uint64_t align) = 0;

  /// \brief Stores a pointer into memory
  /// \sa storeIntToMem
  virtual Expr storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                             unsigned byteSz, uint64_t align) = 0;

  /// \brief Returns an expression corresponding to a load from memory
  ///
  /// \param[in] ptr is the pointer being dereferenced
  /// \param[in] mem is the memory value being read from
  /// \param[in] ty is the type of value being loaded
  /// \param[in] align is the known alignment of the load
  virtual Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const llvm::Type &ty,
                                uint64_t align) = 0;

  virtual Expr storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn,
                               const llvm::Type &ty, uint32_t align) = 0;

  /// \brief Executes symbolic memset with a concrete length
  virtual Expr MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                      uint32_t align) = 0;

  /// \brief Executes symbolic memcpy with concrete length
  virtual Expr MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, Expr memTrsfrRead,
                      uint32_t align) = 0;

  /// \brief Executes symbolic memcpy from physical memory with concrete length
  virtual Expr MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                       uint32_t align = 0) = 0;

  /// \brief Executes inttoptr conversion
  virtual PtrTy inttoptr(Expr intVal, const Type &intTy,
                         const Type &ptrTy) const = 0;

  /// \brief Executes ptrtoint conversion
  virtual Expr ptrtoint(PtrTy ptr, const Type &ptrTy,
                        const Type &intTy) const = 0;

  virtual Expr ptrUlt(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrSlt(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrUle(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrSle(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrUgt(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrSgt(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrUge(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrSge(PtrTy p1, PtrTy p2) const = 0;

  /// \brief Checks if two pointers are equal.
  virtual Expr ptrEq(PtrTy p1, PtrTy p2) const = 0;
  virtual Expr ptrNe(PtrTy p1, PtrTy p2) const = 0;

  virtual Expr ptrSub(PtrTy p1, PtrTy p2) const = 0;

  /// \brief Computes a pointer corresponding to the gep instruction
  virtual PtrTy gep(PtrTy ptr, gep_type_iterator it,
                    gep_type_iterator end) const = 0;

  /// \brief Called when a function is entered for the first time
  virtual void onFunctionEntry(const Function &fn) = 0;

  /// \brief Called when a module entered for the first time
  virtual void onModuleEntry(const Module &M) = 0;

  /// \brief Debug helper
  virtual void dumpGlobalsMap() = 0;

  virtual std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv) = 0;

  virtual Expr zeroedMemory() const = 0;

  /// \brief Checks if \p a <= b <= c.
  Expr ptrInRangeCheck(PtrTy a, PtrTy b, PtrTy c) {
    return mk<AND>(ptrUle(a, b), ptrUle(b, c));
  }
  /// \brief Calculates an offset of a pointer from its base.
  Expr ptrOffsetFromBase(PtrTy base, PtrTy ptr) { return ptrSub(ptr, base); }

  uint32_t getAlignment(const llvm::Value &v) const { return m_alignment; }

  /// \brief returns a constant that represents zero-initilized memory region
};

OpSemMemManager *mkRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas = false);

OpSemMemManager *mkFatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas = false);

/// \Brief Base class for memory representation
class OpSemMemRepr {
protected:
  OpSemMemManager &m_memManager;
  Bv2OpSemContext &m_ctx;
  ExprFactory &m_efac;
  static constexpr unsigned m_BitsPerByte = 8;

public:
  OpSemMemRepr(OpSemMemManager &memManager, Bv2OpSemContext &ctx)
      : m_memManager(memManager), m_ctx(ctx), m_efac(ctx.getExprFactory()) {}
  virtual ~OpSemMemRepr() = default;

  virtual Expr coerce(Expr sort, Expr val) = 0;
  virtual Expr loadAlignedWordFromMem(Expr ptr, Expr mem) = 0;
  virtual Expr storeAlignedWordToMem(Expr val, Expr ptr, Expr ptrSort,
                                     Expr mem) = 0;

  virtual Expr MemSet(Expr ptr, Expr _val, unsigned len, Expr mem,
                      unsigned wordSzInBytes, Expr ptrSort, uint32_t align) = 0;
  virtual Expr MemCpy(Expr dPtr, Expr sPtr, unsigned len, Expr memTrsfrRead,
                      unsigned wordSzInBytes, Expr ptrSort, uint32_t align) = 0;
  virtual Expr MemFill(Expr dPtr, char *sPtr, unsigned len, Expr mem,
                       unsigned wordSzInBytes, Expr ptrSort,
                       uint32_t align) = 0;
};

/// \brief Represent memory regions by logical arrays
class OpSemMemArrayRepr : public OpSemMemRepr {
public:
  OpSemMemArrayRepr(OpSemMemManager &memManager, Bv2OpSemContext &ctx)
      : OpSemMemRepr(memManager, ctx) {}

  Expr coerce(Expr _, Expr val) override { return val; }

  Expr loadAlignedWordFromMem(Expr ptr, Expr mem) override {
    return op::array::select(mem, ptr);
  }

  Expr storeAlignedWordToMem(Expr val, Expr ptr, Expr ptrSort,
                             Expr mem) override {
    (void)ptrSort;
    return op::array::store(mem, ptr, val);
  }

  Expr MemSet(Expr ptr, Expr _val, unsigned len, Expr mem,
              unsigned wordSzInBytes, Expr ptrSort, uint32_t align) override;
  Expr MemCpy(Expr dPtr, Expr sPtr, unsigned len, Expr memTrsfrRead,
              unsigned wordSzInBytes, Expr ptrSort, uint32_t align) override;
  Expr MemFill(Expr dPtr, char *sPtr, unsigned len, Expr mem,
               unsigned wordSzInBytes, Expr ptrSort, uint32_t align) override;
};

/// \brief Represent memory regions by lambda functions
class OpSemMemLambdaRepr : public OpSemMemRepr {
public:
  OpSemMemLambdaRepr(OpSemMemManager &memManager, Bv2OpSemContext &ctx)
      : OpSemMemRepr(memManager, ctx) {}

  Expr coerce(Expr sort, Expr val) override {
    return isOp<ARRAY_TY>(sort) ? coerceArrayToLambda(val) : val;
  }

  Expr loadAlignedWordFromMem(Expr ptr, Expr mem) override {
    return bind::fapp(mem, ptr);
  }

  Expr storeAlignedWordToMem(Expr val, Expr ptr, Expr ptrSort,
                             Expr mem) override;
  Expr MemSet(Expr ptr, Expr _val, unsigned len, Expr mem,
              unsigned wordSzInBytes, Expr ptrSort, uint32_t align) override;
  Expr MemCpy(Expr dPtr, Expr sPtr, unsigned len, Expr memTrsfrRead,
              unsigned wordSzInBytes, Expr ptrSort, uint32_t align) override;
  Expr MemFill(Expr dPtr, char *sPtr, unsigned len, Expr mem,
               unsigned wordSzInBytes, Expr ptrSort, uint32_t align) override;

private:
  Expr coerceArrayToLambda(Expr arrVal);
  Expr makeLinearITE(Expr addr, const ExprVector &ptrKeys,
                     const ExprVector &vals, Expr fallback);
};

/// Evaluates constant expressions
class ConstantExprEvaluator {
  const DataLayout &m_td;
  Bv2OpSemContext *m_ctx;

  const DataLayout &getDataLayout() const { return m_td; }

  bool hasContext() const { return m_ctx; }
  Bv2OpSemContext &getContext() {
    assert(m_ctx);
    return *m_ctx;
  }
  /// \brief Stores a value in \p Val to memory pointed by \p Ptr. The store
  /// is of type \p Ty
  void storeValueToMemory(const GenericValue &Val, GenericValue *Ptr, Type *Ty);

public:
  ConstantExprEvaluator(const DataLayout &td) : m_td(td), m_ctx(nullptr) {}
  void setContext(Bv2OpSemContext &ctx) { m_ctx = &ctx; }

  /// \brief Evaluate a constant expression
  Optional<GenericValue> evaluate(const Constant *C);
  Optional<GenericValue> operator()(const Constant *c) { return evaluate(c); }

  /// \brief Initialize given memory with the value of a constant expression
  /// from: llvm/lib/ExecutionEngine/ExecutionEngine.cpp
  void initMemory(const Constant *Init, void *Addr);
};

} // namespace details
} // namespace seahorn
