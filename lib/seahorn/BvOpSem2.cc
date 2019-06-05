#include "seahorn/BvOpSem2.hh"
#include "llvm/IR/GetElementPtrTypeIterator.h"

#include "seahorn/Support/CFG.hh"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Format.h"
#include "llvm/Support/MathExtras.h"

#include "seahorn/Support/SeaDebug.h"
#include "ufo/ExprLlvm.hpp"
#include "llvm/CodeGen/IntrinsicLowering.h"

using namespace seahorn;
using namespace llvm;

using gep_type_iterator = generic_gep_type_iterator<>;

static llvm::cl::opt<unsigned>
    WordSize("horn-bv2-word-size", llvm::cl::desc("Word size in bytes: 1, 4"),
             cl::init(4));

static llvm::cl::opt<unsigned>
    PtrSize("horn-bv2-ptr-size", llvm::cl::desc("Pointer size in bytes: 4"),
            cl::init(4), cl::Hidden);

static llvm::cl::opt<bool> EnableUniqueScalars2(
    "horn-bv2-singleton-aliases",
    llvm::cl::desc("Treat singleton alias sets as scalar values"),
    cl::init(true));

static llvm::cl::opt<bool> InferMemSafety2(
    "horn-bv2-use-mem-safety",
    llvm::cl::desc("Rely on memory safety assumptions such as "
                   "successful load/store imply validity of their arguments"),
    cl::init(true), cl::Hidden);

static llvm::cl::opt<bool> IgnoreCalloc2(
    "horn-bv2-ignore-calloc",
    llvm::cl::desc(
        "Treat calloc same as malloc, ignore that memory is initialized"),
    cl::init(false), cl::Hidden);

static llvm::cl::opt<bool> EnableModelExternalCalls2(
    "horn-bv2-enable-external-calls",
    llvm::cl::desc("Model external function call as an uninterpreted function"),
    llvm::cl::init(false));

static llvm::cl::list<std::string> IgnoreExternalFunctions2(
    "horn-bv2-ignore-external-functions",
    llvm::cl::desc(
        "These functions are not modeled as uninterpreted functions"),
    llvm::cl::ZeroOrMore, llvm::cl::CommaSeparated);

namespace {
const Value *extractUniqueScalar(CallSite &cs) {
  if (!EnableUniqueScalars2)
    return nullptr;
  else
    return seahorn::shadow_dsa::extractUniqueScalar(cs);
}

const Value *extractUniqueScalar(const CallInst *ci) {
  if (!EnableUniqueScalars2)
    return nullptr;
  else
    return seahorn::shadow_dsa::extractUniqueScalar(ci);
}

bool isShadowMem(const Value &V, const Value **out) {
  const Value *scalar;
  bool res = seahorn::shadow_dsa::isShadowMem(V, &scalar);
  if (EnableUniqueScalars2 && out)
    *out = scalar;
  return res;
}

const seahorn::details::Bv2OpSemContext &const_ctx(const OpSemContext &_ctx);
} // namespace

namespace {
/// \brief Work-arround for a bug in llvm::CallSite::getCalledFunction
/// properly handle bitcast
Function *getCalledFunction(CallSite &CS) {
  Function *fn = CS.getCalledFunction();
  if (fn) return fn;

  Value *v = CS.getCalledValue();
  if (v) v = v->stripPointerCasts();
  fn = dyn_cast<Function>(v);

  return fn;
}

}
namespace seahorn {
namespace details {
class OpSemMemManager;

/// \brief Operational Semantics Context, a.k.a. Semantic Machine
/// Keeps track of the state of the current semantic machine and provides
/// API to manipulate the machine.
class Bv2OpSemContext : public OpSemContext {
  friend class OpSemBase;

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
  /// \brief 1-bit bit-vector set to 1
  Expr trueBv;
  /// \brief 1-bit bit-vector set to 0
  Expr falseBv;
  /// \brief bit-precise representation of null pointer
  Expr nullBv;
  /// \brief bit-precise representation of maximum pointer value
  Expr maxPtrE;

public:
  /// \brief Create a new context with given semantics, values, and side
  Bv2OpSemContext(Bv2OpSem &sem, SymStore &values, ExprVector &side);
  /// \brief Clone a context with possibly new values and side condition
  /// \sa Bv2OpSem::fork
  Bv2OpSemContext(SymStore &values, ExprVector &side,
                  const Bv2OpSemContext &other);
  Bv2OpSemContext(const Bv2OpSemContext &) = delete;
  ~Bv2OpSemContext() override = default;

  /// \brief Returns size of a memory word
  unsigned wordSzInBytes() const;
  /// \brief Returns size in bits of a memory word
  unsigned wordSzInBits() const { return wordSzInBytes() * 8; }
  /// \brief Returns size of a pointer in bits
  unsigned ptrSzInBits() const;

  /// \brief Converts bool expression to bit-vector expression
  Expr boolToBv(Expr b);
  /// \brief Converts bit-vector expression to bool expression
  Expr bvToBool(Expr b);

  /// \brief Returns the memory manager
  OpSemMemManager *getMemManager() { return m_memManager.get(); }

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
  void onBasicBlockEntry(const BasicBlock &bb) override {
    if (!m_func)
      m_func = bb.getParent();
    assert(m_func == bb.getParent());
    if (m_bb)
      m_prev = m_bb;
    m_bb = &bb;
    m_inst = bb.begin();
  }

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

/// \brief Memory manager for OpSem machine
class OpSemMemManager {

  /// \brief Allocation information
  struct AllocInfo {
    /// \brief numeric ID
    unsigned m_id;
    /// \brief Start address of the allocation
    unsigned m_start;
    /// \brief End address of the allocation
    unsigned m_end;
    /// \brief Size of the allocation
    unsigned m_sz;

    AllocInfo(unsigned id, unsigned start, unsigned end, unsigned sz)
        : m_id(id), m_start(start), m_end(end), m_sz(sz) {}
  };

  /// \brief Allocation information for functions whose address is taken
  struct FuncAllocInfo {
    /// \brief Pointer to llvm::Function descriptor of the function
    const Function *m_fn;
    /// \brief Start address of the allocation
    unsigned m_start;
    /// \brief End address of the allocation
    unsigned m_end;

    FuncAllocInfo(const Function &fn, unsigned start, unsigned end)
        : m_fn(&fn), m_start(start), m_end(end) {}
  };

  /// \brief Allocation information for a global variable
  struct GlobalAllocInfo {
    /// \brief Pointer to llvm::GlobalVariable descriptor
    const GlobalVariable *m_gv;
    /// \brief Start of allocation
    unsigned m_start;
    /// \brief End of allocation
    unsigned m_end;
    /// \brief Size of allocation
    unsigned m_sz;

    /// \brief Uninitialized memory for the value of the global on the host
    /// machine
    char *m_mem;
    GlobalAllocInfo(const GlobalVariable &gv, unsigned start, unsigned end,
                    unsigned sz)
        : m_gv(&gv), m_start(start), m_end(end), m_sz(sz) {

      m_mem = static_cast<char *>(::operator new(sz));
    }

    char *getMemory() { return m_mem; }
  };

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

  /// \brief Base name for non-deterministic allocation
  Expr m_allocaName;
  /// \brief Base name for non-deterministic pointer
  Expr m_freshPtrName;

  /// \brief All known stack allocations
  std::vector<AllocInfo> m_allocas;
  /// \brief All known code allocations
  std::vector<FuncAllocInfo> m_funcs;
  /// \brief All known global allocations
  std::vector<GlobalAllocInfo> m_globals;

  /// \brief Register that contains the value of the stack pointer on
  /// function entry
  Expr m_sp0;

  /// \brief Source of unique identifiers
  mutable unsigned m_id;

  /// \brief A null pointer expression (cache)
  Expr m_nullPtr;

// TODO: turn into user-controlled parameters
#define MAX_STACK_ADDR 0xC0000000
#define MIN_STACK_ADDR (MAX_STACK_ADDR - 9437184)
#define TEXT_SEGMENT_START 0x08048000

public:
  OpSemMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx)
      : m_sem(sem), m_ctx(ctx), m_efac(ctx.getExprFactory()), m_ptrSz(PtrSize),
        m_wordSz(WordSize), m_alignment(m_wordSz),
        m_allocaName(mkTerm<std::string>("sea.alloca", m_efac)),
        m_freshPtrName(mkTerm<std::string>("sea.ptr", m_efac)), m_id(0) {
    assert((m_wordSz == 1 || m_wordSz == 4) && "Untested word size");
    assert((m_ptrSz == 4) && "Untested pointer size");
    m_nullPtr = bv::bvnum(0, ptrSzInBits(), m_efac);
    m_sp0 = bv::bvConst(mkTerm<std::string>("sea.sp0", m_efac), ptrSzInBits());
    m_ctx.declareRegister(m_sp0);
  }

  /// Right now everything is an expression. In the future, we might have other
  /// types for PtrTy, such as a tuple of expressions
  using PtrTy = Expr;

  unsigned ptrSzInBits() const { return m_ptrSz * 8; }
  unsigned wordSzInBytes() const { return m_wordSz; }
  unsigned wordSzInBits() const { return m_wordSz * 8; }

  /// \brief Creates a non-deterministic pointer that is aligned
  ///
  /// Top bits of the pointer are named by \p name and last \c log2(align) bits
  /// are set to zero
  PtrTy mkAlignedPtr(Expr name, uint32_t align) const {
    unsigned alignBits = llvm::Log2_32(align);
    return bv::concat(bv::bvConst(name, ptrSzInBits() - alignBits),
                      bv::bvnum(0, alignBits, m_efac));
  }

  /// \brief Returns sort of a pointer register for an instruction
  Expr mkPtrRegisterSort(const Instruction &inst) const {
    const Type *ty = inst.getType();
    assert(ty);
    unsigned sz = m_sem.sizeInBits(*ty);
    assert(ty->isPointerTy());
    assert(sz == ptrSzInBits());

    return bv::bvsort(m_sem.sizeInBits(*ty), m_efac);
  }

  /// \brief Returns sort of a pointer register for a function pointer
  Expr mkPtrRegisterSort(const Function &fn) const {
    return bv::bvsort(ptrSzInBits(), m_efac);
  }

  /// \brief Returns sort of a pointer register for a global pointer
  Expr mkPtrRegisterSort(const GlobalVariable &gv) const {
    return bv::bvsort(ptrSzInBits(), m_efac);
  }

  /// \brief Returns sort of memory-holding register for an instruction
  Expr mkMemRegisterSort(const Instruction &inst) const {
    Expr ptrTy = bv::bvsort(ptrSzInBits(), m_efac);
    Expr valTy = bv::bvsort(wordSzInBits(), m_efac);
    return sort::arrayTy(ptrTy, valTy);
  }

  /// \brief Returns a fresh aligned pointer value
  PtrTy freshPtr() {
    Expr name = op::variant::variant(m_id++, m_freshPtrName);
    return mkAlignedPtr(name, m_alignment);
  }

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  PtrTy salloc(unsigned bytes, uint32_t align = 0) {

    align = std::max(align, m_alignment);
    unsigned start = m_allocas.empty() ? 0 : m_allocas.back().m_end;
    start = llvm::alignTo(start, align);

    unsigned end = start + bytes;
    end = llvm::alignTo(end, align);

    m_allocas.emplace_back(m_allocas.size() + 1, start, end, bytes);

    Expr name = op::variant::variant(m_allocas.back().m_id, m_allocaName);

    return mkStackPtr(name, m_allocas.back());
  }

  /// \brief Returns a pointer value for a given stack allocation
  PtrTy mkStackPtr(Expr name, AllocInfo &allocInfo) {
    Expr res = m_ctx.read(m_sp0);
    res = mk<BSUB>(res, bv::bvnum(allocInfo.m_end, ptrSzInBits(), m_efac));
    return res;
  }

  /// \brief Allocates memory on the stack and returns a pointer to it
  PtrTy salloc(Expr bytes, unsigned align = 0) {
    LOG("opsem", WARN << "unsound handling of dynamically "
                         "sized stack allocation of "
                      << bytes << " bytes";);
    return freshPtr();
  }

  /// \brief Address at which heap starts (initial value of \c brk)
  unsigned brk0Addr() {
    if (!m_globals.empty())
      return m_globals.back().m_end;
    if (!m_funcs.empty())
      return m_funcs.back().m_end;
    return TEXT_SEGMENT_START;
  }

  /// \brief Pointer to start of the heap
  PtrTy brk0Ptr() { return bv::bvnum(brk0Addr(), ptrSzInBits(), m_efac); }

  /// \brief Allocates memory on the heap and returns a pointer to it
  PtrTy halloc(unsigned _bytes, unsigned align = 0) {
    Expr res = freshPtr();

    unsigned bytes = llvm::alignTo(_bytes, std::max(align, m_alignment));

    // -- pointer is in the heap: between brk at the beginning and end of stack
    m_ctx.addSide(mk<BULT>(
        res, bv::bvnum(MIN_STACK_ADDR - bytes, ptrSzInBits(), m_efac)));
    m_ctx.addSide(mk<BUGT>(res, brk0Ptr()));
    return res;
  }

  /// \brief Allocates memory on the heap and returns pointer to it
  PtrTy halloc(Expr bytes, unsigned align = 0) {
    Expr res = freshPtr();

    // -- pointer is in the heap: between brk at the beginning and end of stack
    m_ctx.addSide(
        mk<BULT>(res, bv::bvnum(MIN_STACK_ADDR, ptrSzInBits(), m_efac)));
    m_ctx.addSide(mk<BUGT>(res, brk0Ptr()));
    // TODO: take size of pointer into account,
    // it cannot be that close to the stack
    return res;
  }

  /// \brief Allocates memory in global (data/bss) segment for given global
  PtrTy galloc(const GlobalVariable &gv, unsigned align = 0) {
    uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());

    unsigned start =
        !m_globals.empty()
            ? m_globals.back().m_end
            : (m_funcs.empty() ? TEXT_SEGMENT_START : m_funcs.back().m_end);

    start = llvm::alignTo(start, std::max(align, m_alignment));
    unsigned end = llvm::alignTo(start + gvSz, std::max(align, m_alignment));
    m_globals.emplace_back(gv, start, end, gvSz);
    m_sem.initMemory(gv.getInitializer(), m_globals.back().getMemory());
    return bv::bvnum(start, ptrSzInBits(), m_efac);
  }

  /// \brief Allocates memory in code segment for the code of a given function
  PtrTy falloc(const Function &fn) {
    assert(m_globals.empty() && "Cannot allocate functions after globals");
    unsigned start = m_funcs.empty() ? 0x08048000 : m_funcs.back().m_end;
    unsigned end = llvm::alignTo(start + 4, m_alignment);
    m_funcs.emplace_back(fn, start, end);
    return bv::bvnum(start, ptrSzInBits(), m_efac);
  }

  /// \brief Returns a function pointer value for a given function
  PtrTy getPtrToFunction(const Function &F) {
    return bv::bvnum(getFunctionAddr(F), ptrSzInBits(), m_efac);
  }

  /// \brief Returns an address at which a given function resides
  unsigned getFunctionAddr(const Function &F) {
    for (auto &fi : m_funcs)
      if (fi.m_fn == &F)
        return fi.m_start;
    falloc(F);
    return m_funcs.back().m_start;
  }

  /// \brief Returns a pointer to a global variable
  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv) {
    return bv::bvnum(getGlobalVariableAddr(gv), ptrSzInBits(), m_efac);
  }

  /// \brief Returns an address of a global variable
  unsigned getGlobalVariableAddr(const GlobalVariable &gv) {
    for (auto &gi : m_globals)
      if (gi.m_gv == &gv)
        return gi.m_start;

    galloc(gv);
    return m_globals.back().m_start;
  }

  /// \brief Returns initial value of a global variable
  ///
  /// Returns (nullptr, 0) if the global variable has no known initializer
  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const GlobalVariable &gv) {
    for (auto &gi : m_globals) {
      if (gi.m_gv == &gv)
        return std::make_pair(gi.m_mem, gi.m_sz);
    }
    return std::make_pair(nullptr, 0);
  }

  /// \brief Loads an integer of a given size from memory register
  ///
  /// \param[in] ptr pointer being accessed
  /// \param[in] memReg memory register into which \p ptr points
  /// \param[in] byteSz size of the integer in bytes
  /// \param[in] align known alignment of \p ptr
  /// \return symbolic value of the read integer
  Expr loadIntFromMem(PtrTy ptr, Expr memReg, unsigned byteSz, uint64_t align) {
    Expr mem = m_ctx.read(memReg);
    SmallVector<Expr, 16> words;
    // -- read all words
    for (unsigned i = 0; i < byteSz; i += wordSzInBytes()) {
      words.push_back(loadAlignedWordFromMem(ptrAdd(ptr, i), mem));
    }

    assert(!words.empty());

    // -- concatenate the words together into a singe value
    Expr res;
    for (Expr &w : words)
      res = res ? bv::concat(w, res) : w;

    assert(res);
    assert(byteSz > wordSzInBytes() || words.size() == 1);
    // -- extract actual bytes read (if fewer than word)
    if (byteSz < wordSzInBytes())
      res = bv::extract(byteSz * 8 - 1, 0, res);

    return res;
  }

  /// \brief Loads a pointer stored in memory
  /// \sa loadIntFromMem
  PtrTy loadPtrFromMem(PtrTy ptr, Expr memReg, unsigned byteSz,
                       uint64_t align) {
    return loadIntFromMem(ptr, memReg, byteSz, align);
  }

  /// \brief Loads one word from memory pointed by \p ptr
  Expr loadAlignedWordFromMem(PtrTy ptr, Expr mem) {
    return op::array::select(mem, ptr);
  }

  /// \brief Pointer addition with numeric offset
  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const {
    if (_offset == 0)
      return ptr;
    mpz_class offset(_offset);
    return mk<BADD>(ptr, bv::bvnum(offset, ptrSzInBits(), ptr->efac()));
  }

  /// \brief Pointer addition with symbolic offset
  PtrTy ptrAdd(PtrTy ptr, Expr offset) const {
    if (bv::isBvNum(offset)) {
      mpz_class _offset = bv::toMpz(offset);
      return ptrAdd(ptr, _offset.get_si());
    }
    return mk<BADD>(ptr, offset);
  }

  /// \brief Stores an integer into memory
  ///
  /// Returns an expression describing the state of memory in \c memReadReg
  /// after the store
  /// \sa loadIntFromMem
  Expr storeIntToMem(Expr _val, PtrTy ptr, Expr memReadReg, unsigned byteSz,
                     uint64_t align) {
    Expr val = _val;
    Expr mem = m_ctx.read(memReadReg);

    SmallVector<Expr, 16> words;
    if (byteSz == wordSzInBytes()) {
      words.push_back(val);
    } else if (byteSz < wordSzInBytes()) {
      val = bv::zext(val, wordSzInBytes() * 8);
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
      res = storeAlignedWordToMem(words[i], ptrAdd(ptr, i * wordSzInBytes()),
                                  mem);
      mem = res;
    }

    return res;
  }

  /// \brief Stores a pointer into memory
  /// \sa storeIntToMem
  Expr storePtrToMem(PtrTy val, PtrTy ptr, Expr memReadReg, unsigned byteSz,
                     uint64_t align) {
    return storeIntToMem(val, ptr, memReadReg, byteSz, align);
  }

  /// \brief Writes one aligned word into memory
  Expr storeAlignedWordToMem(Expr val, PtrTy ptr, Expr mem) {
    return op::array::store(mem, ptr, val);
  }

  /// \brief Creates bit-vector of a given width filled with 0
  Expr mkZeroE(unsigned width, ExprFactory &efac) {
    return bv::bvnum(0, width, efac);
  }
  // breif Creates a bit-vector for number 1 of a given width
  Expr mkOneE(unsigned width, ExprFactory &efac) {
    return bv::bvnum(1, width, efac);
  }

  /// \brief Returns an expression corresponding to a load from memory
  ///
  /// \param[in] ptr is the pointer being dereferenced
  /// \param[in] memReg is the memory register being read
  /// \param[in] ty is the type of value being loaded
  /// \param[in] align is the known alignment of the load
  Expr loadValueFromMem(PtrTy ptr, Expr memReg, const llvm::Type &ty,
                        uint64_t align) {
    const unsigned byteSz =
        m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
    ExprFactory &efac = ptr->efac();

    Expr res;
    switch (ty.getTypeID()) {
    case Type::IntegerTyID:
      res = loadIntFromMem(ptr, memReg, byteSz, align);
      if (res && ty.isIntegerTy(1))
        res = boolop::lneg(mk<EQ>(res, mkZeroE(byteSz * 8, efac)));
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
    default:
      SmallString<256> msg;
      raw_svector_ostream out(msg);
      out << "Loading from type: " << ty << " is not supported\n";
      report_fatal_error(out.str());
    }
    return res;
  }

  Expr storeValueToMem(Expr _val, PtrTy ptr, Expr memReadReg, Expr memWriteReg,
                       const llvm::Type &ty, uint32_t align) {
    assert(ptr);
    Expr val = _val;
    const unsigned byteSz =
        m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
    ExprFactory &efac = ptr->efac();

    Expr res;
    switch (ty.getTypeID()) {
    case Type::IntegerTyID:
      if (ty.isIntegerTy(1)) {
        val = boolop::lite(val, mkOneE(byteSz * 8, efac),
                           mkZeroE(byteSz * 8, efac));
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
    default:
      SmallString<256> msg;
      raw_svector_ostream out(msg);
      out << "Loading from type: " << ty << " is not supported\n";
      report_fatal_error(out.str());
    }
    m_ctx.write(memWriteReg, res);
    return res;
  }

  /// \brief Executes symbolic memset with a concrete length
  Expr MemSet(PtrTy ptr, Expr _val, unsigned len, Expr memReadReg,
              Expr memWriteReg, uint32_t align) {
    Expr res;

    unsigned width;
    if (bv::isBvNum(_val, width) && width == 8) {
      unsigned val = bv::toMpz(_val).get_ui();
      val = val & 0xFF;
      switch (wordSzInBytes()) {
      case 1:
        break;
      case 4:
        assert(align == 0 || align == 4);
        val = val | (val << 8) | (val << 16) | (val << 24);
        break;
      default:
        llvm::report_fatal_error("Unsupported word sz for memset\n");
      }

      res = m_ctx.read(memReadReg);
      for (unsigned i = 0; i < len; i += wordSzInBytes()) {
        Expr idx = ptr;
        if (i > 0)
          idx = mk<BADD>(ptr, bv::bvnum(i, ptrSzInBits(), m_efac));
        res =
            op::array::store(res, idx, bv::bvnum(val, wordSzInBits(), m_efac));
      }
      m_ctx.write(memWriteReg, res);
    }

    return res;
  }

  /// \brief Executes symbolic memcpy with concrete length
  Expr MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, Expr memTrsfrReadReg,
              Expr memReadReg, Expr memWriteReg, uint32_t align) {
    Expr res;

    if (wordSzInBytes() == 1 || (wordSzInBytes() == 4 && align == 4)) {
      Expr srcMem = m_ctx.read(memTrsfrReadReg);
      res = srcMem;
      for (unsigned i = 0; i < len; i += wordSzInBytes()) {
        Expr dIdx = dPtr;
        Expr sIdx = sPtr;
        if (i > 0) {
          Expr offset = bv::bvnum(i, ptrSzInBits(), m_efac);
          dIdx = mk<BADD>(dPtr, offset);
          sIdx = mk<BADD>(sPtr, offset);
        }
        Expr val = op::array::select(srcMem, sIdx);
        res = op::array::store(res, dIdx, val);
      }
      m_ctx.write(memWriteReg, res);
    }
    return res;
  }

  /// \brief Executes symbolic memcpy from physical memory with concrete length
  Expr MemFill(PtrTy dPtr, char *sPtr, unsigned len, uint32_t align = 0) {
    // same alignment behavior as galloc - default is word size of machine, can
    // only be increased
    align = std::max(align, m_alignment);
    Expr res = m_ctx.read(m_ctx.getMemReadRegister());
    unsigned sem_word_sz = wordSzInBytes();
    for (unsigned i = 0; i < len; i += sem_word_sz) {
      Expr offset = bv::bvnum(i, ptrSzInBits(), m_efac);
      Expr dIdx = i == 0 ? dPtr : mk<BADD>(dPtr, offset);
      unsigned word = 0;
      for (int byte = sem_word_sz - 1; byte >= 0; byte--) {
        word = word << 8;
        if (i + byte < len)
          word += sPtr[i + byte];
      }
      Expr val = bv::bvnum(word, sem_word_sz * 8, m_efac);
      res = op::array::store(res, dIdx, val);
    }
    m_ctx.write(m_ctx.getMemWriteRegister(), res);
    return res;
  }

  /// \brief Executes inttoptr conversion
  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const {
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

  /// \brief Executes ptrtoint conversion
  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const {
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
  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const {
    Expr offset = m_sem.symbolicIndexedOffset(it, end, m_ctx);
    return offset ? ptrAdd(ptr, offset) : Expr();
  }

  /// \brief Called when a function is entered for the first time
  void onFunctionEntry(const Function &fn) {
    Expr res = m_ctx.read(m_sp0);

    // XXX hard coded values
    // align of 4
    m_ctx.addDef(bv::bvnum(0, 2, m_efac), bv::extract(2 - 1, 0, res));
    // 3GB upper limit
    m_ctx.addSide(
        mk<BULE>(res, bv::bvnum(MAX_STACK_ADDR, ptrSzInBits(), m_efac)));
    // 9MB stack
    m_ctx.addSide(
        mk<BUGE>(res, bv::bvnum(MIN_STACK_ADDR, ptrSzInBits(), m_efac)));
  }

  /// \breif Called when a module entered for the first time
  void onModuleEntry(const Module &M) {}

  /// \brief Debug helper
  void dumpGlobalsMap() {
    errs() << "Functions: \n";
    if (m_funcs.empty())
      errs() << "NONE\n";
    for (auto &fi : m_funcs) {
      errs() << llvm::format_hex(fi.m_start, 16, true) << " @"
             << fi.m_fn->getName() << "\n";
    }

    errs() << "Globals: \n";
    if (m_globals.empty())
      errs() << "NONE\n";
    for (auto &gi : m_globals) {
      errs() << llvm::format_hex(gi.m_start, 16, true) << " @"
             << gi.m_gv->getName() << "\n";
    }
  }
};

struct OpSemBase {
  Bv2OpSemContext &m_ctx;
  ExprFactory &m_efac;
  Bv2OpSem &m_sem;

  Expr trueE;
  Expr falseE;
  Expr zeroE;
  Expr oneE;
  Expr trueBv;
  Expr falseBv;
  Expr nullBv;

  /// -- start of current memory segment
  Expr m_cur_startMem;
  /// -- end of current memory segment
  Expr m_cur_endMem;

  Expr m_maxPtrE;

  OpSemBase(Bv2OpSemContext &ctx, Bv2OpSem &sem)
      : m_ctx(ctx), m_efac(m_ctx.getExprFactory()), m_sem(sem),
        m_cur_startMem(nullptr), m_cur_endMem(nullptr), m_maxPtrE(nullptr) {

    trueE = m_ctx.m_trueE;
    falseE = m_ctx.m_falseE;
    zeroE = m_ctx.zeroE;
    oneE = m_ctx.oneE;
    trueBv = m_ctx.trueBv;
    falseBv = m_ctx.falseBv;
    nullBv = m_ctx.nullBv;

    m_maxPtrE = m_ctx.maxPtrE;

    // XXX AG: this is probably wrong since instances of OpSemBase are created
    // XXX AG: for each instruction, not just once per function
    // XXX AG: but not an issue at this point since function calls are not handled by the semantics 
    // -- first two arguments are reserved for error flag,
    // -- the other is function activation
    // ctx.pushParameter(falseE);
    // ctx.pushParameter(falseE);
    // ctx.pushParameter(falseE);
  }

  unsigned ptrSzInBits() { return m_ctx.ptrSzInBits(); }

  Expr read(const Value &v) {
    if (m_sem.isSkipped(v))
      return Expr();

    Expr reg;
    if (reg = m_ctx.getRegister(v))
      return m_ctx.read(reg);

    if (const Constant *cv = dyn_cast<Constant>(&v)) {
      return m_ctx.getConstantValue(*cv);
    }

    reg = m_ctx.mkRegister(v);
    if (reg)
      return m_ctx.read(reg);

    errs() << "Error: failed to read a value for: " << v << "\n";
    llvm_unreachable(nullptr);
  }

  Expr lookup(const Value &v) { return m_sem.getOperandValue(v, m_ctx); }

  Expr havoc(const Value &v) {
    if (m_sem.isSkipped(v))
      return Expr();

    Expr reg;
    if (reg = m_ctx.getRegister(v))
      return m_ctx.havoc(reg);

    assert(!isa<Constant>(v));
    reg = m_ctx.mkRegister(v);
    if (reg)
      return m_ctx.havoc(reg);
    errs() << "Error: failed to havoc: " << v << "\n";
    llvm_unreachable(nullptr);
  }

  void write(const Value &v, Expr val) {
    if (m_sem.isSkipped(v))
      return;

    Expr reg;
    if (reg = m_ctx.getRegister(v))
      m_ctx.write(reg, val);
    else {
      assert(!isa<Constant>(v));
      reg = m_ctx.mkRegister(v);
      if (reg)
        m_ctx.write(reg, val);
      else {
        errs() << "Error: failed to write: " << v << "\n";
        llvm_unreachable(nullptr);
      }
    }
  }

  /// convert bv1 to bool
  Expr bvToBool(Expr bv) { return m_ctx.bvToBool(bv); }
  Expr boolToBv(Expr b) { return m_ctx.boolToBv(b); }

  void setValue(const Value &v, Expr e) {
    if (e)
      write(v, e);
    else {
      m_sem.unhandledValue(v, m_ctx);
      havoc(v);
    }
  }
};

class OpSemVisitor : public InstVisitor<OpSemVisitor>, OpSemBase {
public:
  OpSemVisitor(Bv2OpSemContext &ctx, Bv2OpSem &sem) : OpSemBase(ctx, sem) {}

  // Opcode Implementations
  void visitReturnInst(ReturnInst &I) {
    // -- skip return argument of main
    if (I.getParent()->getParent()->getName().equals("main"))
      return;

    // read the operand of return instruction so that the read is observable
    // b symstore
    if (I.getNumOperands() > 0)
      lookup(*I.getOperand(0));
  }
  void visitBranchInst(BranchInst &I) {
    if (I.isConditional())
      lookup(*I.getCondition());
  }

  void visitSwitchInst(SwitchInst &I) {
    llvm_unreachable("switch instructions are not supported. Must be lowered.");
  }
  void visitIndirectBrInst(IndirectBrInst &I) { llvm_unreachable(nullptr); }

  void visitBinaryOperator(BinaryOperator &I) {
    Type *ty = I.getOperand(0)->getType();
    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    if (op0 && op1) {
      switch (I.getOpcode()) {
      default:
        errs() << "Unknown binary operator: " << I << "\n";
        llvm_unreachable(nullptr);
        break;
      case Instruction::Add:
        res = mk<BADD>(op0, op1);
        break;
      case Instruction::Sub:
        res = mk<BSUB>(op0, op1);
        break;
      case Instruction::Mul:
        res = mk<BMUL>(op0, op1);
        break;
      case Instruction::FAdd:
        break;
      case Instruction::FSub:
        break;
      case Instruction::FMul:
        break;
      case Instruction::FDiv:
        break;
      case Instruction::FRem:
        break;
      case Instruction::UDiv:
        res = mk<BUDIV>(op0, op1);
        break;
      case Instruction::SDiv:
        res = mk<BSDIV>(op0, op1);
        break;
      case Instruction::URem:
        res = mk<BUREM>(op0, op1);
        break;
      case Instruction::SRem:
        res = mk<BSREM>(op0, op1);
        break;
      case Instruction::And:
        res = ty->isIntegerTy(1) ? mk<AND>(op0, op1) : mk<BAND>(op0, op1);
        break;
      case Instruction::Or:
        res = ty->isIntegerTy(1) ? mk<OR>(op0, op1) : mk<BOR>(op0, op1);
        break;
      case Instruction::Xor:
        res = ty->isIntegerTy(1) ? mk<XOR>(op0, op1) : mk<BXOR>(op0, op1);
        break;
      }
    }

    setValue(I, res);
  }

  void visitICmpInst(ICmpInst &I) {
    Type *ty = I.getOperand(0)->getType();
    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      switch (I.getPredicate()) {
      case ICmpInst::ICMP_EQ:
        res = executeICMP_EQ(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_NE:
        res = executeICMP_NE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_ULT:
        res = executeICMP_ULT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SLT:
        res = executeICMP_SLT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_UGT:
        res = executeICMP_UGT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SGT:
        res = executeICMP_SGT(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_ULE:
        res = executeICMP_ULE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SLE:
        res = executeICMP_SLE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_UGE:
        res = executeICMP_UGE(op0, op1, ty, m_ctx);
        break;
      case ICmpInst::ICMP_SGE:
        res = executeICMP_SGE(op0, op1, ty, m_ctx);
        break;
      default:
        errs() << "Unknown ICMP predicate" << I;
        llvm_unreachable(nullptr);
      }
    }
    setValue(I, res);
  }

  void visitFCmpInst(FCmpInst &I) { llvm_unreachable(nullptr); }

  void visitAllocaInst(AllocaInst &I) {
    Type *ty = I.getType()->getElementType();
    unsigned typeSz = (size_t)m_sem.getTD().getTypeAllocSize(ty);

    Expr addr;
    if (const Constant *cv = dyn_cast<const Constant>(I.getOperand(0))) {
      auto ogv = m_sem.getConstantValue(cv);
      if (!ogv.hasValue()) {
        llvm_unreachable(nullptr);
      }
      unsigned nElts = ogv.getValue().IntVal.getZExtValue();
      unsigned memSz = typeSz * nElts;
      LOG("opsem", errs() << "Alloca of " << memSz << " bytes: " << I << "\n";);
      addr = m_ctx.getMemManager()->salloc(memSz);
    } else {
      Expr nElts = lookup(*I.getOperand(0));
      LOG("opsem", errs() << "Alloca of " << nElts << "*" << typeSz
                          << " bytes: " << I << "\n";);
      WARN << "alloca of symbolic size is treated as non-deterministic";
      addr = m_ctx.getMemManager()->freshPtr();
    }

    setValue(I, addr);
  }

  void visitLoadInst(LoadInst &I) {
    setValue(I, executeLoadInst(*I.getPointerOperand(), I.getAlignment(),
                                I.getType(), m_ctx));
  }
  void visitStoreInst(StoreInst &I) {
    executeStoreInst(*I.getValueOperand(), *I.getPointerOperand(),
                     I.getAlignment(), m_ctx);
  }

  void visitGetElementPtrInst(GetElementPtrInst &I) {
    Expr val = executeGEPOperation(*I.getPointerOperand(), gep_type_begin(I),
                                   gep_type_end(I), m_ctx);
    setValue(I, val);
  }

  void visitPHINode(PHINode &PN) {
    // -- there is a special visitor for PHINodes
    llvm_unreachable("PHI nodes are handled by a different visitor!");
  }
  void visitTruncInst(TruncInst &I) {
    setValue(I, executeTruncInst(*I.getOperand(0), *I.getType(), m_ctx));
  }
  void visitZExtInst(ZExtInst &I) {
    setValue(I, executeZExtInst(*I.getOperand(0), *I.getType(), m_ctx));
  }
  void visitSExtInst(SExtInst &I) {
    setValue(I, executeSExtInst(*I.getOperand(0), *I.getType(), m_ctx));
  }

  // floating point instructions
  void visitFPTruncInst(FPTruncInst &I) { llvm_unreachable(nullptr); }
  void visitFPExtInst(FPExtInst &I) { llvm_unreachable(nullptr); }
  void visitUIToFPInst(UIToFPInst &I) { llvm_unreachable(nullptr); }
  void visitSIToFPInst(SIToFPInst &I) { llvm_unreachable(nullptr); }
  void visitFPToUIInst(FPToUIInst &I) { llvm_unreachable(nullptr); }
  void visitFPToSIInst(FPToSIInst &I) { llvm_unreachable(nullptr); }

  void visitPtrToIntInst(PtrToIntInst &I) {
    setValue(I, executePtrToIntInst(*I.getOperand(0), I.getType(), m_ctx));
  }
  void visitIntToPtrInst(IntToPtrInst &I) {
    setValue(I, executeIntToPtrInst(*I.getOperand(0), I.getType(), m_ctx));
  }

  void visitBitCastInst(BitCastInst &I) {
    setValue(I, executeBitCastInst(*I.getOperand(0), I.getType(), m_ctx));
  }

  void visitSelectInst(SelectInst &I) {
    Type *ty = I.getOperand(0)->getType();
    Expr cond = lookup(*I.getCondition());
    Expr op0 = lookup(*I.getTrueValue());
    Expr op1 = lookup(*I.getFalseValue());

    Expr res = executeSelectInst(cond, op0, op1, ty, m_ctx);
    setValue(I, res);
  }

  void visitCallSite(CallSite CS) {
    if (!CS.isCall()) {
      llvm_unreachable("invoke instructions "
                       "are not supported and must be lowered");
    }

    const Function *f = getCalledFunction(CS);
    if (!f) {
      visitIndirectCall(CS);
      return;
    }

    // -- should be handled by visitIntrinsicInst
    assert(!f->isIntrinsic());

    if (f->getName().startswith("verifier.assume")) {
      visitVerifierAssumeCall(CS);
      return;
    }

    if (f->getName().equals("calloc")) {
      visitCallocCall(CS);
      return;
    }

    if (CS.getInstruction()->getMetadata("shadow.mem")) {
      visitShadowMemCall(CS);
      return;
    }

    if (f->getName().startswith("shadow.mem")) {
      WARN << "missing metadata on shadow.mem functions. "
              "Probably using old ShadowMem pass. "
              "Some features might not work as expected";
      visitShadowMemCall(CS);
      return;
    }

    if (f->isDeclaration()) {
      if (f->arg_empty() && (f->getName().startswith("nd") ||
                             f->getName().startswith("nondet.") ||
                             f->getName().startswith("verifier.nondet") ||
                             f->getName().startswith("__VERIFIER_nondet")))
        visitNondetCall(CS);
      else
        visitExternalCall(CS);
      return;
    }

    if (m_sem.hasFunctionInfo(*f)) {
      visitKnownFunctionCall(CS);
    }

    ERR << "unhandled call instruction: " << *CS.getInstruction();
    llvm_unreachable(nullptr);
  }

  void visitIndirectCall(CallSite CS) {
    // treat as non-det and issue a warning
    setValue(*CS.getInstruction(), Expr());
  }

  void visitVerifierAssumeCall(CallSite CS) {
    Function &f = *getCalledFunction(CS);

    Expr op = lookup(*CS.getArgument(0));
    assert(op);

    if (f.getName().equals("verifier.assume.not"))
      op = boolop::lneg(op);

    if (!isOpX<TRUE>(op)) {
      m_ctx.addSideSafe(boolop::lor(
          m_ctx.read(m_sem.errorFlag(*(CS.getInstruction()->getParent()))),
          op));
    }
  }

  void visitCallocCall(CallSite CS) {
    if (!m_ctx.getMemReadRegister() || !m_ctx.getMemReadRegister()) {
      LOG("opsem", WARN << "treating calloc() as nop";);
      return;
    }

    assert(!m_ctx.isMemScalar());

    if (IgnoreCalloc2) {
      LOG("opsem", WARN << "treating calloc() as malloc()";);
      m_ctx.addDef(m_ctx.read(m_ctx.getMemWriteRegister()),
                   m_ctx.read(m_ctx.getMemReadRegister()));
    } else {
      LOG("opsem", WARN << "allowing calloc() to "
                           "zero initialize ALL of its memory region\n";);
      // TODO: move into MemManager
      m_ctx.addDef(
          m_ctx.read(m_ctx.getMemWriteRegister()),
          op::array::constArray(bv::bvsort(ptrSzInBits(), m_efac), nullBv));
    }

    // get a fresh pointer
    const Instruction &inst = *CS.getInstruction();
    setValue(inst, havoc(inst));
  }

  void visitShadowMemCall(CallSite CS) {
    const Instruction &inst = *CS.getInstruction();

    const Function &F = *getCalledFunction(CS);
    if (F.getName().equals("shadow.mem.init")) {
      unsigned id = shadow_dsa::getShadowId(CS);
      assert(id >= 0);
      setValue(inst, havoc(inst));
      return;
    }

    if (F.getName().equals("shadow.mem.load")) {
      const Value &v = *CS.getArgument(1);
      Expr reg = m_ctx.mkRegister(v);
      m_ctx.read(reg);
      m_ctx.setMemReadRegister(reg);
      m_ctx.setMemScalar(extractUniqueScalar(CS) != nullptr);
      return;
    }

    if (F.getName().equals("shadow.mem.trsfr.load")) {
      const Value &v = *CS.getArgument(1);
      Expr reg = m_ctx.mkRegister(v);
      m_ctx.read(reg);
      m_ctx.setMemTrsfrReadReg(reg);
      if (extractUniqueScalar(CS) != nullptr) {
        WARN << "unexpected unique scalar in mem.trsfr.load: " << inst;
        llvm_unreachable(nullptr);
      }
      return;
    }

    if (F.getName().equals("shadow.mem.store")) {
      Expr memOut = m_ctx.mkRegister(inst);
      Expr memIn = m_ctx.getRegister(*CS.getArgument(1));
      m_ctx.read(memIn);
      setValue(inst, havoc(inst));

      m_ctx.setMemReadRegister(memIn);
      m_ctx.setMemWriteRegister(memOut);
      m_ctx.setMemScalar(extractUniqueScalar(CS) != nullptr);

      LOG("opsem.mem.store", errs() << "mem.store: " << inst << "\n";
          errs() << "arg1: " << *CS.getArgument(1) << "\n";
          errs() << "mem.store: memIn is " << *memIn << " memOut is " << *memOut
                 << "\n";);
      return;
    }

    if (F.getName().equals("shadow.mem.arg.ref")) {
      m_ctx.pushParameter(lookup(*CS.getArgument(1)));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.mod")) {
      m_ctx.pushParameter(lookup(*CS.getArgument(1)));
      Expr reg = m_ctx.mkRegister(inst);
      assert(reg);
      m_ctx.pushParameter(m_ctx.havoc(reg));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.new")) {
      Expr reg = m_ctx.mkRegister(inst);
      m_ctx.pushParameter(m_ctx.havoc(reg));
      return;
    }

    const Function &PF = *inst.getParent()->getParent();

    if (F.getName().equals("shadow.mem.in")) {
      if (PF.getName().equals("main"))
        setValue(inst, havoc(inst));
      else
        lookup(*CS.getArgument(1));
      return;
    }

    if (F.getName().equals("shadow.mem.out")) {
      if (PF.getName().equals("main"))
        setValue(inst, havoc(inst));
      else
        lookup(*CS.getArgument(1));
      return;
    }

    if (F.getName().equals("shadow.mem.arg.init")) {
      if (PF.getName().equals("main"))
        setValue(inst, havoc(inst));
      return;
    }

    if (F.getName().equals("shadow.mem.global.init")) {
      Expr memOut = m_ctx.mkRegister(inst);
      Expr memIn = m_ctx.getRegister(*CS.getArgument(1));
      m_ctx.read(memIn);
      setValue(inst, lookup(*CS.getArgument(1)));

      m_ctx.setMemReadRegister(memIn);
      m_ctx.setMemWriteRegister(memOut);

      LOG("opsem.mem.global.init", errs()
                                       << "mem.global.init: " << inst << "\n";
          errs() << "arg1: " << *CS.getArgument(1) << "\n";
          errs() << "memIn: " << *memIn << ", memOut: " << *memOut << "\n";);

      Value *gVal = (*CS.getArgument(2)).stripPointerCasts();
      if (auto *gv = dyn_cast<llvm::GlobalVariable>(gVal)) {
        auto gvVal = m_ctx.getGlobalVariableInitValue(*gv);
        if (gvVal.first) {
          m_ctx.MemFill(lookup(*gv), gvVal.first, gvVal.second);
        }
      } else {
        WARN << "skipping global var init of " << inst << " to " << *gVal
             << "\n";
      }
      return;
    }

    WARN << "unknown shadow.mem call: " << inst;
    llvm_unreachable(nullptr);
  }

  void visitNondetCall(CallSite CS) {
    const Instruction &inst = *CS.getInstruction();
    if (!inst.getType()->isVoidTy()) {
      setValue(inst, m_ctx.havoc(m_ctx.mkRegister(inst)));
    }
  }
  void visitExternalCall(CallSite CS) {
    Function &F = *getCalledFunction(CS);
    if (F.getFunctionType()->getReturnType()->isVoidTy())
      return;

    const Instruction &inst = *CS.getInstruction();

    if (!EnableModelExternalCalls2 ||
        std::find(IgnoreExternalFunctions2.begin(),
                  IgnoreExternalFunctions2.end(),
                  F.getName()) != IgnoreExternalFunctions2.end()) {
      setValue(inst, Expr());
      return;
    }

    // Treat the call as an uninterpreted function
    Expr res;
    ExprVector fargs;
    ExprVector sorts;
    fargs.reserve(CS.arg_size());
    sorts.reserve(CS.arg_size());

    bool is_typed = true;
    for (auto &a : CS.args()) {
      if (m_sem.isSkipped(*a))
        continue;

      Expr e = lookup(*a);
      if (!e)
        continue;
      fargs.push_back(e);
      Expr s = bind::typeOf(e);
      if (!s) {
        // bind::typeOf is partially defined
        is_typed = false;
        break;
      }
      sorts.push_back(s);
    }

    if (is_typed) {
      // return type of the function
      Expr symReg = m_ctx.mkRegister(inst);
      Expr ty = bind::typeOf(symReg);
      if (!ty) {
        is_typed = false;
      } else {
        sorts.push_back(ty);
      }
    }

    if (is_typed) {
      LOG("opsem", errs() << "Modelling " << inst
                          << " with an uninterpreted function\n";);
      Expr name = mkTerm<const Function *>(getCalledFunction(CS), m_efac);
      Expr d = bind::fdecl(name, sorts);
      res = bind::fapp(d, fargs);
    }

    setValue(inst, res);
  }

  void visitKnownFunctionCall(CallSite CS) {
    const Function &F = *getCalledFunction(CS);
    const FunctionInfo &fi = m_sem.getFunctionInfo(F);
    const Instruction &inst = *CS.getInstruction();
    const BasicBlock &BB = *inst.getParent();

    // enabled
    m_ctx.setParameter(0, m_ctx.getActLit()); // activation literal
    // error flag in
    m_ctx.setParameter(1, m_ctx.read(m_sem.errorFlag(BB)));
    // error flag out
    m_ctx.setParameter(2, m_ctx.havoc(m_sem.errorFlag(BB)));
    for (const Argument *arg : fi.args)
      m_ctx.pushParameter(lookup(*CS.getArgument(arg->getArgNo())));
    for (const GlobalVariable *gv : fi.globals)
      m_ctx.pushParameter(lookup(*gv));

    if (fi.ret) {
      Expr reg = m_ctx.mkRegister(inst);
      Expr v = m_ctx.havoc(reg);
      setValue(inst, v);
      m_ctx.pushParameter(v);
    }

    LOG("arg_error",

        if (m_ctx.getParameters().size() != bind::domainSz(fi.sumPred)) {
          const Instruction &I = *CS.getInstruction();
          const Function &PF = *BB.getParent();
          errs() << "Call instruction: " << I << "\n";
          errs() << "Caller: " << PF << "\n";
          errs() << "Callee: " << F << "\n";
          // errs () << "Sum predicate: " << *fi.sumPred << "\n";
          errs() << "m_ctx.getParameters().size: "
                 << m_ctx.getParameters().size() << "\n";
          errs() << "Domain size: " << bind::domainSz(fi.sumPred) << "\n";
          errs() << "m_ctx.getParameters()\n";
          for (auto r : m_ctx.getParameters())
            errs() << *r << "\n";
          errs() << "regions: " << fi.regions.size()
                 << " args: " << fi.args.size()
                 << " globals: " << fi.globals.size() << " ret: " << fi.ret
                 << "\n";
          errs() << "regions\n";
          for (auto r : fi.regions)
            errs() << *r << "\n";
          errs() << "args\n";
          for (auto r : fi.args)
            errs() << *r << "\n";
          errs() << "globals\n";
          for (auto r : fi.globals)
            errs() << *r << "\n";
          if (fi.ret)
            errs() << "ret: " << *fi.ret << "\n";
        });

    assert(m_ctx.getParameters().size() == bind::domainSz(fi.sumPred));
    m_ctx.addSide(bind::fapp(fi.sumPred, m_ctx.getParameters()));

    m_ctx.resetParameters();
    m_ctx.pushParameter(falseE);
    m_ctx.pushParameter(falseE);
    m_ctx.pushParameter(falseE);
  }

  void visitIntrinsicInst(IntrinsicInst &I) {
    switch (I.getIntrinsicID()) {
    case Intrinsic::bswap: {
      BasicBlock::iterator me(&I);
      auto *parent = I.getParent();
      bool atBegin(parent->begin() == me);
      if (!atBegin)
        --me;
      IntrinsicLowering IL(m_sem.getDataLayout());
      IL.LowerIntrinsicCall(&I);
      if (atBegin) {
        m_ctx.setInstruction(*parent->begin());
      } else {
        m_ctx.setInstruction(*me);
        ++m_ctx;
      }
    } break;
    default:
      // interpret by non-determinism (and a warning)
      if (!I.getType()->isVoidTy())
        setValue(I, Expr());
    }
  }

  void visitDbgDeclareInst(DbgDeclareInst &I) { /* nothing */
  }
  void visitDbgValueInst(DbgValueInst &I) { /* nothing */
  }
  void visitDbgInfoIntrinsic(DbgInfoIntrinsic &I) { /* nothing */
  }

  void visitMemSetInst(MemSetInst &I) {
    executeMemSetInst(*I.getDest(), *I.getValue(), *I.getLength(),
                      I.getAlignment(), m_ctx);
  }
  void visitMemCpyInst(MemCpyInst &I) {
    executeMemCpyInst(*I.getDest(), *I.getSource(), *I.getLength(),
                      I.getAlignment(), m_ctx);
  }

  void visitMemMoveInst(MemMoveInst &I) {
    LOG("opsem", errs() << "Skipping memmove: " << I << "\n";);
  }
  void visitMemTransferInst(MemTransferInst &I) {
    LOG("opsem", errs() << "Unknown memtransfer: " << I << "\n";);
    llvm_unreachable(nullptr);
  }

  void visitMemIntrinsic(MemIntrinsic &I) {
    LOG("opsem", errs() << "Unknown memory intrinsic: " << I << "\n";);
    llvm_unreachable(nullptr);
  }

  void visitVAStartInst(VAStartInst &I) { llvm_unreachable(nullptr); }
  void visitVAEndInst(VAEndInst &I) { llvm_unreachable(nullptr); }
  void visitVACopyInst(VACopyInst &I) { llvm_unreachable(nullptr); }

  void visitUnreachableInst(UnreachableInst &I) { /* do nothing */
  }

  void visitShl(BinaryOperator &I) {
    Type *ty = I.getType();
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      res = mk<BSHL>(op0, op1);
    }

    setValue(I, res);
  }

  void visitLShr(BinaryOperator &I) {
    Type *ty = I.getType();
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      res = mk<BLSHR>(op0, op1);
    }

    setValue(I, res);
  }

  void visitAShr(BinaryOperator &I) {
    Type *ty = I.getType();
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(*I.getOperand(0));
    Expr op1 = lookup(*I.getOperand(1));
    Expr res;

    if (op0 && op1) {
      res = mk<BASHR>(op0, op1);
    }

    setValue(I, res);
  }

  void visitVAArgInst(VAArgInst &I) { llvm_unreachable(nullptr); }

  void visitExtractElementInst(ExtractElementInst &I) {
    llvm_unreachable(nullptr);
  }
  void visitInsertElementInst(InsertElementInst &I) {
    llvm_unreachable(nullptr);
  }
  void visitShuffleVectorInst(ShuffleVectorInst &I) {
    llvm_unreachable(nullptr);
  }

  // void visitExtractValueInst(ExtractValueInst &I);
  // void visitInsertValueInst(InsertValueInst &I);

  void visitInstruction(Instruction &I) {
    ERR << I;
    llvm_unreachable("No semantics to this instruction yet!");
  }

  Expr executeSelectInst(Expr cond, Expr op0, Expr op1, Type *ty,
                         Bv2OpSemContext &ctx) {
    if (ty->isVectorTy()) {
      llvm_unreachable(nullptr);
    }
    return cond && op0 && op1 ? mk<ITE>(cond, op0, op1) : Expr(0);
  }

  Expr executeTruncInst(const Value &v, const Type &ty, Bv2OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();

    uint64_t width = m_sem.sizeInBits(ty);
    Expr res = bv::extract(width - 1, 0, op0);
    return ty.isIntegerTy(1) ? bvToBool(res) : res;
  }

  Expr executeZExtInst(const Value &v, const Type &ty, Bv2OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();
    if (v.getType()->isIntegerTy(1))
      op0 = boolToBv(op0);
    return bv::zext(op0, m_sem.sizeInBits(ty));
  }

  Expr executeSExtInst(const Value &v, const Type &ty, Bv2OpSemContext &ctx) {
    if (v.getType()->isVectorTy()) {
      llvm_unreachable(nullptr);
    }

    Expr op0 = lookup(v);
    if (!op0)
      return Expr();
    if (v.getType()->isIntegerTy(1))
      op0 = boolToBv(op0);
    return bv::sext(op0, m_sem.sizeInBits(ty));
  }

  Expr executeICMP_EQ(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<EQ>(op0, op1);
    case Type::PointerTyID:
      return mk<EQ>(op0, op1);
    default:
      errs() << "Unhandled ICMP_EQ predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_NE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<NEQ>(op0, op1);
    case Type::PointerTyID:
      return mk<NEQ>(op0, op1);
    default:
      errs() << "Unhandled ICMP_NE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_ULT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BULT>(op0, op1);
    case Type::PointerTyID:
      return mk<BULT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_ULT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SLT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BSLT>(op0, op1);
    case Type::PointerTyID:
      return mk<BSLT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_UGT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BUGT>(op0, op1);
    case Type::PointerTyID:
      return mk<BUGT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_UGT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SGT(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {

    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      if (ty->isIntegerTy(1)) {
        if (isOpX<TRUE>(op1))
          // icmp sgt op0, i1 true  == !op0
          return boolop::lneg(op0);
        else
          return bvToBool(mk<BSGT>(boolToBv(op0), boolToBv(op1)));
      }
      return mk<BSGT>(op0, op1);
    case Type::PointerTyID:
      return mk<BSGT>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SGT predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_ULE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BULE>(op0, op1);
    case Type::PointerTyID:
      return mk<BULE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_ULE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SLE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BSLE>(op0, op1);
    case Type::PointerTyID:
      return mk<BSLE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_UGE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BUGE>(op0, op1);
    case Type::PointerTyID:
      return mk<BUGE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SLE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executeICMP_SGE(Expr op0, Expr op1, Type *ty, Bv2OpSemContext &ctx) {
    switch (ty->getTypeID()) {
    case Type::IntegerTyID:
      return mk<BSGE>(op0, op1);
    case Type::PointerTyID:
      return mk<BSGE>(op0, op1);
    default:
      errs() << "Unhandled ICMP_SGE predicate: " << *ty << "\n";
      llvm_unreachable(nullptr);
    }
    llvm_unreachable(nullptr);
  }

  Expr executePtrToIntInst(const Value &op, const Type *ty,
                           Bv2OpSemContext &ctx) {
    Expr res = lookup(op);
    if (!res)
      return Expr();
    return ctx.ptrtoint(res, *op.getType(), *ty);
  }

  Expr executeIntToPtrInst(const Value &op, const Type *ty,
                           Bv2OpSemContext &ctx) {
    Expr res = lookup(op);
    if (!res)
      return Expr();
    return ctx.inttoptr(res, *op.getType(), *ty);
  }

  Expr executeGEPOperation(const Value &ptr, gep_type_iterator it,
                           gep_type_iterator end, Bv2OpSemContext &ctx) {
    Expr addr = lookup(ptr);
    return addr ? ctx.gep(addr, it, end) : Expr();
  }

  Expr executeLoadInst(const Value &addr, unsigned alignment, const Type *ty,
                       Bv2OpSemContext &ctx) {
    Expr res;
    if (!ctx.getMemReadRegister())
      return res;

    if (ctx.isMemScalar()) {
      res = ctx.read(ctx.getMemReadRegister());
      if (ty->isIntegerTy(1))
        res = bvToBool(res);
    } else if (Expr op0 = lookup(addr)) {
      res = ctx.loadValueFromMem(op0, *ty, alignment);
    }

    ctx.setMemReadRegister(Expr());
    return res;
  }

  Expr executeStoreInst(const Value &val, const Value &addr, unsigned alignment,
                        Bv2OpSemContext &ctx) {

    if (!ctx.getMemReadRegister() || !ctx.getMemWriteRegister() ||
        m_sem.isSkipped(val)) {
      LOG("opsem",
          errs() << "Skipping store to " << addr << " of " << val << "\n";);
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return Expr();
    }

    Expr v = lookup(val);
    Expr res;
    if (v && ctx.isMemScalar()) {
      if (val.getType()->isIntegerTy(1))
        v = boolToBv(v);
      res = v;
      ctx.write(ctx.getMemWriteRegister(), res);
    } else {
      Expr p = lookup(addr);
      if (v && p)
        res = m_ctx.storeValueToMem(v, p, *val.getType(), alignment);
    }

    if (!res)
      LOG("opsem",
          errs() << "Skipping store to " << addr << " of " << val << "\n";);

    ctx.setMemReadRegister(Expr());
    ctx.setMemWriteRegister(Expr());
    return res;
  }

  Expr executeMemSetInst(const Value &dst, const Value &val,
                         const Value &length, unsigned alignment,
                         Bv2OpSemContext &ctx) {
    if (!ctx.getMemReadRegister() || !ctx.getMemWriteRegister() ||
        m_sem.isSkipped(dst) || m_sem.isSkipped(val)) {
      LOG("opsem", WARN << "Skipping memset\n");
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return Expr();
    }

    if (ctx.isMemScalar()) {
      ERR << "memset to scalars is not supported";
      llvm_unreachable(nullptr);
    }

    Expr res;
    Expr addr = lookup(dst);

    assert(val.getType()->isIntegerTy(8));
    Expr v = lookup(val);
    Expr len = lookup(length);
    if (v && addr) {
      if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&length)) {
        res = m_ctx.MemSet(addr, v, ci->getZExtValue(), alignment);
      } else
        llvm_unreachable("Unsupported memset with symbolic length");
    }

    if (!res)
      LOG("opsem", errs() << "Skipping memset\n";);

    ctx.setMemReadRegister(Expr());
    ctx.setMemWriteRegister(Expr());
    return res;
  }

  Expr executeMemCpyInst(const Value &dst, const Value &src,
                         const Value &length, unsigned alignment,
                         Bv2OpSemContext &ctx) {
    if (!ctx.getMemReadRegister() || !ctx.getMemWriteRegister() ||
        !ctx.getMemTrsfrReadReg() || m_sem.isSkipped(dst) ||
        m_sem.isSkipped(src)) {
      LOG("opsem", WARN << "skipping memcpy");
      ctx.setMemTrsfrReadReg(Expr());
      ctx.setMemReadRegister(Expr());
      ctx.setMemWriteRegister(Expr());
      return Expr();
    }

    if (ctx.isMemScalar())
      llvm_unreachable("memcpy to scalars is not supported");

    Expr res;
    Expr dstAddr = lookup(dst);
    Expr srcAddr = lookup(src);
    Expr len = lookup(length);
    if (dstAddr && srcAddr) {
      if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&length)) {
        res = m_ctx.MemCpy(dstAddr, srcAddr, ci->getZExtValue(), alignment);
      } else
        llvm_unreachable("Unsupported memcpy with symbolic length");
    }

    if (!res)
      LOG("opsem", errs() << "Skipping memcpy\n";);

    ctx.setMemTrsfrReadReg(Expr());
    ctx.setMemReadRegister(Expr());
    ctx.setMemWriteRegister(Expr());
    return res;
  }

  Expr executeBitCastInst(const Value &op, Type *ty, Bv2OpSemContext &ctx) {
    Type *opTy = op.getType();

    if (opTy->getTypeID() == Type::VectorTyID ||
        ty->getTypeID() == Type::VectorTyID)
      llvm_unreachable("Vector types are unsupported");

    Expr res = lookup(op);
    if (!res)
      return Expr();

    if (ty->isPointerTy())
      return res;

    if (ty->isIntegerTy()) {
      if (opTy->isFloatTy())
        llvm_unreachable("bitcast from float to int is not supported");
      else if (opTy->isDoubleTy())
        llvm_unreachable("bitcast from double to int is not supported");
      else if (opTy->isIntegerTy()) {
        return res;
      } else {
        llvm_unreachable("Invalid bitcast");
      }
    } else if (ty->isFloatTy()) {
      if (opTy->isIntegerTy())
        llvm_unreachable("bitcast to float not supported");
      else
        return res;
    } else if (ty->isDoubleTy()) {
      if (opTy->isIntegerTy())
        llvm_unreachable("bitcast to double not supported");
      else
        return res;
    }

    llvm_unreachable("Invalid bitcast");
  }

  void visitModule(Module &M) {
    LOG("opsem.module", errs() << M << "\n"; );
    m_ctx.onModuleEntry(M);

    for (const Function &fn : M.functions()) {
      if (fn.hasAddressTaken()) {
        // XXX hard-coded. should be based on use
        // XXX some functions have their address taken for llvm.used
        if (fn.getName().equals("verifier.error") ||
            fn.getName().startswith("verifier.assume") ||
            fn.getName().equals("seahorn.fail") ||
            fn.getName().startswith("shadow.mem"))
          continue;
        Expr symReg = m_ctx.mkRegister(fn);
        assert(symReg);
        setValue(fn, m_ctx.getMemManager()->falloc(fn));
      }
    }

    for (const GlobalVariable &gv : M.globals()) {
      if (m_sem.isSkipped(gv))
        continue;
      if (gv.getSection().equals("llvm.metadata")) {
        LOG("opsem", WARN << "Skipping global variable marked "
                             "by llvm.metadata section: @"
                          << gv.getName(););
        continue;
      }
      Expr symReg = m_ctx.mkRegister(gv);
      assert(symReg);
      setValue(gv, m_ctx.getMemManager()->galloc(gv));
    }

    LOG("opsem", m_ctx.getMemManager()->dumpGlobalsMap());
  }

  void visitBasicBlock(BasicBlock &BB) {
    Function &F = *BB.getParent();
    /// -- check if globals need to be initialized
    if (&F.getEntryBlock() == &BB) {
      if (F.getName().equals("main"))
        visitModule(*F.getParent());
      m_ctx.onFunctionEntry(*BB.getParent());
    }

    // read the error flag to make it live
    m_ctx.read(m_sem.errorFlag(BB));
  }
};

struct OpSemPhiVisitor : public InstVisitor<OpSemPhiVisitor>, OpSemBase {
  OpSemPhiVisitor(Bv2OpSemContext &ctx, Bv2OpSem &sem) : OpSemBase(ctx, sem) {}

  void visitBasicBlock(BasicBlock &BB) {
    // -- evaluate all phi-nodes atomically. First read all incoming
    // -- values, then update phi-nodes all together.
    llvm::SmallVector<Expr, 8> ops;

    auto curr = BB.begin();
    if (!isa<PHINode>(curr))
      return;

    // -- evaluate all incoming values in parallel
    for (; PHINode *phi = dyn_cast<PHINode>(curr); ++curr) {
      // skip phi nodes that are not tracked
      if (m_sem.isSkipped(*phi))
        continue;
      const Value &v = *phi->getIncomingValueForBlock(m_ctx.getPrevBb());
      ops.push_back(lookup(v));
    }

    // -- set values to all PHINode registers
    curr = BB.begin();
    for (unsigned i = 0; PHINode *phi = dyn_cast<PHINode>(curr); ++curr) {
      if (m_sem.isSkipped(*phi))
        continue;
      setValue(*phi, ops[i++]);
    }
  }
};
} // namespace details
} // namespace seahorn

namespace seahorn {
namespace details {
Bv2OpSemContext::Bv2OpSemContext(Bv2OpSem &sem, SymStore &values,
                                 ExprVector &side)
    : OpSemContext(values, side), m_sem(sem), m_func(nullptr), m_bb(nullptr),
      m_inst(nullptr), m_prev(nullptr), m_scalar(false) {
  zeroE = mkTerm<mpz_class>(0, efac());
  oneE = mkTerm<mpz_class>(1, efac());
  trueBv = bv::bvnum(1, 1, efac());
  falseBv = bv::bvnum(0, 1, efac());

  setMemManager(new OpSemMemManager(m_sem, *this));
}

Bv2OpSemContext::Bv2OpSemContext(SymStore &values, ExprVector &side,
                                 const Bv2OpSemContext &o)
    : OpSemContext(values, side), m_sem(o.m_sem), m_func(o.m_func),
      m_bb(o.m_bb), m_inst(o.m_inst), m_prev(o.m_prev),
      m_readRegister(o.m_readRegister), m_writeRegister(o.m_writeRegister),
      m_scalar(o.m_scalar), m_trfrReadReg(o.m_trfrReadReg),
      m_fparams(o.m_fparams), m_ignored(o.m_ignored),
      m_registers(o.m_registers), m_memManager(nullptr), m_parent(&o),
      zeroE(o.zeroE), oneE(o.oneE), trueBv(o.trueBv), falseBv(o.falseBv),
      nullBv(o.nullBv), maxPtrE(o.maxPtrE) {
  setActLit(o.getActLit());
}

unsigned Bv2OpSemContext::ptrSzInBits() const {

  assert(m_memManager);
  if (m_parent)
    return m_parent->ptrSzInBits();
  // XXX HACK for refactoring
  return m_memManager ? m_memManager->ptrSzInBits() : 32;
}

void Bv2OpSemContext::setMemManager(OpSemMemManager *man) {
  m_memManager.reset(man);
  // TODO: move into MemManager
  nullBv = bv::bvnum(0, ptrSzInBits(), efac());

  // TODO: move into MemManager
  mpz_class val;
  switch (ptrSzInBits()) {
  case 64:
    // TODO: take alignment into account
    val = 0x000000000FFFFFFF;
    break;
  case 32:
    // TODO: take alignment into account
    val = 0x0FFFFFFF;
    break;
  default:
    LOG("opsem",
        errs() << "Unsupported pointer size: " << ptrSzInBits() << "\n";);
    llvm_unreachable("Unexpected pointer size");
  }
  maxPtrE = bv::bvnum(val, ptrSzInBits(), efac());
}

Expr Bv2OpSemContext::loadValueFromMem(Expr ptr, const llvm::Type &ty,
                                       uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  return m_memManager->loadValueFromMem(ptr, getMemReadRegister(), ty, align);
}

Expr Bv2OpSemContext::storeValueToMem(Expr val, Expr ptr, const llvm::Type &ty,
                                      uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  return m_memManager->storeValueToMem(val, ptr, getMemReadRegister(),
                                       getMemWriteRegister(), ty, align);
}

Expr Bv2OpSemContext::MemSet(Expr ptr, Expr val, unsigned len, uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  return m_memManager->MemSet(ptr, val, len, getMemReadRegister(),
                              getMemWriteRegister(), align);
}

Expr Bv2OpSemContext::MemCpy(Expr dPtr, Expr sPtr, unsigned len,
                             uint32_t align) {
  assert(m_memManager);
  assert(getMemTrsfrReadReg());
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  return m_memManager->MemCpy(dPtr, sPtr, len, getMemTrsfrReadReg(),
                              getMemReadRegister(), getMemWriteRegister(),
                              align);
}

Expr Bv2OpSemContext::MemFill(Expr dPtr, char *sPtr, unsigned len,
                              uint32_t align) {
  assert(m_memManager);
  assert(getMemReadRegister());
  assert(getMemWriteRegister());
  return m_memManager->MemFill(dPtr, sPtr, len, align);
}

Expr Bv2OpSemContext::inttoptr(Expr intValue, const Type &intTy,
                               const Type &ptrTy) const {
  if (m_parent)
    return m_parent->inttoptr(intValue, intTy, ptrTy);
  return m_memManager->inttoptr(intValue, intTy, ptrTy);
}

Expr Bv2OpSemContext::ptrtoint(Expr ptrValue, const Type &ptrTy,
                               const Type &intTy) const {
  assert(m_memManager);
  if (m_parent)
    return m_parent->ptrtoint(ptrValue, ptrTy, intTy);
  return m_memManager->ptrtoint(ptrValue, ptrTy, intTy);
}

Expr Bv2OpSemContext::gep(Expr ptr, gep_type_iterator it,
                          gep_type_iterator end) const {
  if (m_parent)
    return m_parent->gep(ptr, it, end);
  return m_memManager->gep(ptr, it, end);
}

void Bv2OpSemContext::onFunctionEntry(const Function &fn) {
  m_memManager->onFunctionEntry(fn);
}
void Bv2OpSemContext::onModuleEntry(const Module &M) {
  return m_memManager->onModuleEntry(M);
}

void Bv2OpSemContext::declareRegister(Expr v) { m_registers.insert(v); }
bool Bv2OpSemContext::isKnownRegister(Expr v) { return m_registers.count(v); }

Expr Bv2OpSemContext::mkRegister(const llvm::BasicBlock &bb) {
  if (Expr r = getRegister(bb))
    return r;
  Expr reg = bind::boolConst(mkTerm<const BasicBlock *>(&bb, efac()));
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&bb, reg));
  return reg;
}

Expr Bv2OpSemContext::mkPtrRegisterSort(const Instruction &inst) const {
  if (m_parent)
    return m_parent->mkPtrRegisterSort(inst);
  return m_memManager->mkPtrRegisterSort(inst);
}

Expr Bv2OpSemContext::mkPtrRegisterSort(const Function &fn) const {
  if (m_parent)
    return m_parent->mkPtrRegisterSort(fn);
  return m_memManager->mkPtrRegisterSort(fn);
}

Expr Bv2OpSemContext::mkPtrRegisterSort(const GlobalVariable &gv) const {
  if (m_parent)
    return m_parent->mkPtrRegisterSort(gv);
  return m_memManager->mkPtrRegisterSort(gv);
}

Expr Bv2OpSemContext::mkMemRegisterSort(const Instruction &inst) const {
  if (m_parent)
    return m_parent->mkMemRegisterSort(inst);
  return m_memManager->mkMemRegisterSort(inst);
}

Expr Bv2OpSemContext::mkRegister(const llvm::Instruction &inst) {
  if (Expr r = getRegister(inst))
    return r;
  Expr reg;
  // everything else is mapped to a symbolic register with a
  // non-deterministic initial value
  Expr v = mkTerm<const Value *>(&inst, efac());

  // pseudo register corresponding to memory blocks
  const Value *scalar = nullptr;
  if (isShadowMem(inst, &scalar)) {
    // if memory is single cell, allocate regular register
    if (scalar) {
      assert(scalar->getType()->isPointerTy());
      Type &eTy = *cast<PointerType>(scalar->getType())->getElementType();
      // -- create a constant with the name v[scalar]
      reg = bv::bvConst(
          op::array::select(v, mkTerm<const Value *>(scalar, efac())),
          m_sem.sizeInBits(eTy));
    }

    // if tracking memory content, create array-valued register for
    // the pseudo-assignment
    else { //(true /*m_trackLvl >= MEM*/) {
      reg = bind::mkConst(v, mkMemRegisterSort(inst));
    }
  } else {
    const Type &ty = *inst.getType();
    switch (ty.getTypeID()) {
    case Type::IntegerTyID:
      reg = ty.isIntegerTy(1) ? bind::boolConst(v)
                              : bv::bvConst(v, m_sem.sizeInBits(ty));
      break;
    case Type::PointerTyID:
      reg = bind::mkConst(v, mkPtrRegisterSort(inst));
      break;
    default:
      errs() << "Error: unhandled type: " << ty << " of " << inst << "\n";
      llvm_unreachable(nullptr);
    }
  }
  assert(reg);
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&inst, reg));
  return reg;
}

Expr Bv2OpSemContext::mkRegister(const llvm::Function &fn) {
  if (Expr r = getRegister(fn))
    return r;

  Expr reg;
  Expr v = mkTerm<const Value *>(&fn, efac());

  reg = bind::mkConst(v, mkPtrRegisterSort(fn));
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&fn, reg));
  return reg;
}

Expr Bv2OpSemContext::mkRegister(const llvm::GlobalVariable &gv) {
  if (Expr r = getRegister(gv))
    return r;
  Expr reg;
  Expr v = mkTerm<const Value *>(&gv, efac());

  reg = bind::mkConst(v, mkPtrRegisterSort(gv));
  declareRegister(reg);
  m_valueToRegister.insert(std::make_pair(&gv, reg));
  return reg;
}

Expr Bv2OpSemContext::mkRegister(const llvm::Value &v) {
  if (auto const *bb = dyn_cast<llvm::BasicBlock>(&v)) {
    return mkRegister(*bb);
  }
  if (auto const *inst = dyn_cast<llvm::Instruction>(&v)) {
    return mkRegister(*inst);
  }
  if (auto const *fn = dyn_cast<llvm::Function>(&v)) {
    return mkRegister(*fn);
  }
  if (auto const *gv = dyn_cast<llvm::GlobalVariable>(&v)) {
    return mkRegister(*gv);
  }
  ERR << "cannot make symbolic register for " << v << "\n";
  llvm_unreachable(nullptr);
}

Expr Bv2OpSemContext::getConstantValue(const llvm::Constant &c) {
  // -- easy common cases
  if (c.isNullValue() || isa<ConstantPointerNull>(&c)) {
    return c.getType()->isIntegerTy(1)
               ? m_falseE
               : bv::bvnum(0, m_sem.sizeInBits(c), efac());
  } else if (const ConstantInt *ci = dyn_cast<const ConstantInt>(&c)) {
    if (ci->getType()->isIntegerTy(1))
      return ci->isOne() ? m_trueE : m_falseE;

    mpz_class k = toMpz(ci->getValue());
    return bv::bvnum(k, m_sem.sizeInBits(c), efac());
  }

  if (c.getType()->isIntegerTy()) {
    auto GVO = m_sem.getConstantValue(&c);
    if (GVO.hasValue()) {
      GenericValue gv = GVO.getValue();
      mpz_class k = toMpz(gv.IntVal);
      if (c.getType()->isIntegerTy(1)) {
        return k == 1 ? m_trueE : m_falseE;
      } else {
        return bv::bvnum(k, m_sem.sizeInBits(c), efac());
      }
    }
  } else if (c.getType()->isPointerTy()) {
    LOG("opsem", WARN << "unhandled constant pointer " << c;);
  } else {
    LOG("opsem", WARN << "unhandled constant " << c;);
  }
  return Expr();
}

std::pair<char *, unsigned>
Bv2OpSemContext::getGlobalVariableInitValue(const llvm::GlobalVariable &gv) {
  return m_memManager->getGlobalVariableInitValue(gv);
}

Expr Bv2OpSemContext::boolToBv(Expr b) {
  if (isOpX<TRUE>(b))
    return trueBv;
  if (isOpX<FALSE>(b))
    return falseBv;
  return mk<ITE>(b, trueBv, falseBv);
}

Expr Bv2OpSemContext::bvToBool(Expr bv) {
  if (bv == trueBv)
    return m_trueE;
  if (bv == falseBv)
    return m_falseE;
  return mk<EQ>(bv, trueBv);
}
} // namespace details

Bv2OpSem::Bv2OpSem(ExprFactory &efac, Pass &pass, const DataLayout &dl,
                   TrackLevel trackLvl)
    : OperationalSemantics(efac), m_pass(pass), m_trackLvl(trackLvl),
      m_td(&dl) {
  m_canFail = pass.getAnalysisIfAvailable<CanFail>();
  auto *p = pass.getAnalysisIfAvailable<TargetLibraryInfoWrapperPass>();
  if (p)
    m_tli = &p->getTLI();

  // -- hack to get ENode::dump() to compile by forcing a use
  LOG("dump.debug", trueE->dump(););
}

OpSemContextPtr Bv2OpSem::mkContext(SymStore &values, ExprVector &side) {
  return OpSemContextPtr(new details::Bv2OpSemContext(*this, values, side));
}

Bv2OpSem::Bv2OpSem(const Bv2OpSem &o)
    : OperationalSemantics(o), m_pass(o.m_pass), m_trackLvl(o.m_trackLvl),
      m_td(o.m_td), m_canFail(o.m_canFail) {}

Expr Bv2OpSem::errorFlag(const BasicBlock &BB) {
  // -- if BB belongs to a function that cannot fail, errorFlag is always false
  if (m_canFail && !m_canFail->canFail(BB.getParent()))
    return falseE;
  return this->OperationalSemantics::errorFlag(BB);
}

void Bv2OpSem::exec(const BasicBlock &bb, details::Bv2OpSemContext &ctx) {
  ctx.onBasicBlockEntry(bb);

  details::OpSemVisitor v(ctx, *this);
  v.visitBasicBlock(const_cast<BasicBlock &>(bb));
  // skip PHI instructions
  for (; isa<PHINode>(ctx.getCurrentInst()); ++ctx)
    ;

  while (intraStep(ctx)) {
    /* do nothing */;
  }
}

void Bv2OpSem::execPhi(const BasicBlock &bb, const BasicBlock &from,
                       details::Bv2OpSemContext &ctx) {
  ctx.onBasicBlockEntry(bb);
  ctx.setPrevBb(from);
  intraPhi(ctx);
}

Expr Bv2OpSem::symbolicIndexedOffset(gep_type_iterator TI, gep_type_iterator TE,
                                     details::Bv2OpSemContext &ctx) {
  unsigned ptrSz = pointerSizeInBits();

  // numeric offset
  uint64_t noffset = 0;
  // symbolic offset
  Expr soffset;

  for (; TI != TE; ++TI) {
    Value *CurVal = TI.getOperand();
    if (StructType *STy = TI.getStructTypeOrNull()) {
      unsigned fieldNo = cast<ConstantInt>(CurVal)->getZExtValue();
      noffset += fieldOff(STy, fieldNo);
    } else {
      assert(TI.isSequential());
      unsigned sz = storageSize(TI.getIndexedType());
      if (ConstantInt *ci = dyn_cast<ConstantInt>(CurVal)) {
        int64_t arrayIdx = ci->getSExtValue();
        noffset += (uint64_t)arrayIdx * sz;
      } else {
        Expr a = getOperandValue(*CurVal, ctx);
        assert(a);
        a = mk<BMUL>(a, bv::bvnum(sz, ptrSz, m_efac));
        soffset = (soffset ? mk<BADD>(soffset, a) : a);
      }
    }
  }

  Expr res;
  if (noffset > 0)
    res = bv::bvnum(/* cast to make clang on osx happy */
                    (unsigned long int)noffset, ptrSz, m_efac);
  if (soffset)
    res = res ? mk<BADD>(soffset, res) : soffset;

  if (!res) {
    assert(noffset == 0);
    assert(!soffset);
    res = bv::bvnum((unsigned long int)noffset, ptrSz, m_efac);
  }

  return res;
}

unsigned Bv2OpSem::pointerSizeInBits() const {
  return m_td->getPointerSizeInBits();
}

uint64_t Bv2OpSem::sizeInBits(const llvm::Type &t) const {
  return m_td->getTypeSizeInBits(const_cast<llvm::Type *>(&t));
}

uint64_t Bv2OpSem::sizeInBits(const llvm::Value &v) const {
  return sizeInBits(*v.getType());
}

unsigned Bv2OpSem::storageSize(const llvm::Type *t) const {
  return m_td->getTypeStoreSize(const_cast<Type *>(t));
}

unsigned Bv2OpSem::fieldOff(const StructType *t, unsigned field) const {
  return m_td->getStructLayout(const_cast<StructType *>(t))
      ->getElementOffset(field);
}

Expr Bv2OpSem::getOperandValue(const Value &v, details::Bv2OpSemContext &ctx) {
  Expr res;
  if (auto *bb = dyn_cast<BasicBlock>(&v)) {
    Expr reg = ctx.getRegister(*bb);
    if (reg)
      res = ctx.read(reg);
  } else if (auto *fn = dyn_cast<Function>(&v)) {
    if (Expr reg = ctx.getRegister(*fn)) {
      res = ctx.read(reg);
    } else
      res = ctx.getConstantValue(*fn);
  } else if (auto *gv = dyn_cast<GlobalVariable>(&v)) {
    if (Expr reg = ctx.getRegister(*gv)) {
      res = ctx.read(reg);
    } else
      res = ctx.getConstantValue(*gv);
  } else if (auto *cv = dyn_cast<Constant>(&v)) {
    res = ctx.getConstantValue(*cv);
    assert(res);
  } else {
    Expr reg = ctx.getRegister(v);
    if (reg)
      res = ctx.read(reg);
    else
      WARN << "Failed to get register for: " << v << "\n";
  }
  return res;
}

bool Bv2OpSem::isSymReg(Expr v, details::Bv2OpSemContext &C) {
  if (this->OperationalSemantics::isSymReg(v))
    return true;

  if (C.isKnownRegister(v))
    return true;

  // TODO: memStart and memEnd

  // a symbolic register is any expression that resolves to an
  // llvm::Value XXX it might be better to register registers with a
  // SymStore and XXX let register be only expressions that are
  // explicitly marked as registers
  if (!isOpX<FAPP>(v))
    return false;

  Expr u = bind::fname(v);
  u = bind::fname(u);
  if (isOpX<VALUE>(u))
    return true;

  errs() << "Unexpected symbolic value: " << *v << "\n";
  llvm_unreachable(nullptr);
}

const Value &Bv2OpSem::conc(Expr v) const {
  assert(isOpX<FAPP>(v));
  // name of the app
  Expr u = bind::fname(v);
  // name of the fdecl
  u = bind::fname(u);
  assert(isOpX<VALUE>(v));
  return *getTerm<const Value *>(v);
}

bool Bv2OpSem::isSkipped(const Value &v) const {
  // skip shadow.mem instructions if memory is not a unique scalar
  // and we are now ignoring memory instructions
  const Value *scalar = nullptr;
  if (isShadowMem(v, &scalar)) {
    return scalar == nullptr && m_trackLvl < MEM;
  }

  const Type *ty = v.getType();
  if (ty->isPointerTy()) {
    // -- XXX A hack because shadow.mem generates not well formed
    // -- bitcode that contains future references. A register that
    // -- is defined later is used to name a shadow region in the
    // -- beginning of the function. Perhaps there is a better
    // -- solution. For now, we just do not track anything that came
    // -- that way.
    if (v.hasOneUse())
      if (const CallInst *ci = dyn_cast<const CallInst>(*v.user_begin()))
        if (const Function *fn = ci->getCalledFunction())
          if (fn->getName().startswith("shadow.mem"))
            return true;
    return m_trackLvl < PTR;
  }

  // -- explicitly name all types that we support
  // -- TODO: support arrays and struct values
  switch (ty->getTypeID()) {
  case Type::VoidTyID:
    return false;
  case Type::HalfTyID:
  case Type::FloatTyID:
  case Type::DoubleTyID:
  case Type::X86_FP80TyID:
  case Type::FP128TyID:
  case Type::PPC_FP128TyID:
    // floating types are not supported
    // TODO: integrate floating branch
    return true;
  case Type::LabelTyID:
    ERR << "Unexpected label type";
    llvm_unreachable(nullptr);
  case Type::MetadataTyID:
    ERR << "Unexpected metadata type";
    llvm_unreachable(nullptr);
  case Type::X86_MMXTyID:
    LOG("opsem", WARN << "Unsupported X86 type\n");
    return true;
  case Type::TokenTyID:
    llvm_unreachable("Unexpected token type");
  case Type::IntegerTyID:
    return false;
  case Type::FunctionTyID:
    llvm_unreachable("Unexpected function type");
  case Type::StructTyID:
    LOG("opsem", WARN << "Unsupported struct type\n";);
    return true;
  case Type::ArrayTyID:
    LOG("opsem", WARN << "Unsupported array type\n";);
    return true;
  case Type::PointerTyID:
    // -- pointers are handled earlier in the procedure
    llvm_unreachable(nullptr);
  case Type::VectorTyID:
    LOG("opsem", WARN << "Unsupported vector type\n";);
    return true;
  default:
    LOG("opsem", ERR << "Unknown type: " << *ty << "\n";);
    llvm_unreachable(nullptr);
  }
  llvm_unreachable(nullptr);
}

/// \brief Executes one intra-procedural instructions in the current
/// context. Returns false if there are no more instructions to
/// execute after the last one
bool Bv2OpSem::intraStep(details::Bv2OpSemContext &C) {
  if (C.isAtBbEnd())
    return false;

  const Instruction &inst = C.getCurrentInst();

  // -- update instruction pointer in the context --
  // branch instructions must be executed to read the condition
  // on which the branch depends. This does not execute the branch
  // itself and does not advance instruction pointer in the context
  bool res = true;
  if (!isa<TerminatorInst>(&inst)) {
    ++C;
  } else if (isa<BranchInst>(&inst)) {
    res = false;
  } else {
    return false;
  }

  // -- execute instruction --

  // if instruction is skipped, execution it is a noop
  if (isSkipped(inst)) {
    skipInst(inst, C);
    return true;
  }

  details::OpSemVisitor v(C, *this);
  v.visit(const_cast<Instruction &>(inst));
  return res;
}

void Bv2OpSem::intraPhi(details::Bv2OpSemContext &C) {
  assert(C.getPrevBb());

  // act is ignored since phi node only introduces a definition
  details::OpSemPhiVisitor v(C, *this);
  v.visitBasicBlock(const_cast<BasicBlock &>(*C.getCurrBb()));
}
/// \brief Executes one intra-procedural branch instruction in the
/// current context. Assumes that current instruction is a branch
void Bv2OpSem::intraBr(details::Bv2OpSemContext &C, const BasicBlock &dst) {
  const BranchInst *br = dyn_cast<const BranchInst>(&C.getCurrentInst());
  if (!br)
    return;

  // next instruction
  ++C;

  if (br->isConditional()) {
    const Value &c = *br->getCondition();
    if (const Constant *cv = dyn_cast<const Constant>(&c)) {
      auto gv = getConstantValue(cv);
      assert(gv.hasValue());
      if (gv->IntVal.isOneValue() && br->getSuccessor(0) != &dst ||
          gv->IntVal.isNullValue() && br->getSuccessor(1) != &dst) {
        C.resetSide();
        C.addSideSafe(C.read(errorFlag(*C.getCurrBb())));
      }
    } else if (Expr target = getOperandValue(c, C)) {
      Expr cond = br->getSuccessor(0) == &dst ? target : mk<NEG>(target);
      cond = boolop::lor(C.read(errorFlag(*C.getCurrBb())), cond);
      C.addSideSafe(cond);
      C.onBasicBlockEntry(dst);
    }
  } else {
    if (br->getSuccessor(0) != &dst) {
      C.resetSide();
      C.addSideSafe(C.read(errorFlag(*C.getCurrBb())));
    } else {
      C.onBasicBlockEntry(dst);
    }
  }
}

void Bv2OpSem::skipInst(const Instruction &inst,
                        details::Bv2OpSemContext &ctx) {
  const Value *s;
  if (isShadowMem(inst, &s))
    return;
  if (ctx.isIgnored(inst))
    return;
  ctx.ignore(inst);
  LOG("opsem", WARN << "skipping instruction: " << inst << " @ "
                    << inst.getParent()->getName() << " in "
                    << inst.getParent()->getParent()->getName(););
}

void Bv2OpSem::unhandledValue(const Value &v, details::Bv2OpSemContext &ctx) {
  if (const Instruction *inst = dyn_cast<const Instruction>(&v))
    return unhandledInst(*inst, ctx);
  LOG("opsem", WARN << "unhandled value: " << v;);
}
void Bv2OpSem::unhandledInst(const Instruction &inst,
                             details::Bv2OpSemContext &ctx) {
  if (ctx.isIgnored(inst))
    return;
  ctx.ignore(inst);
  LOG("opsem", WARN << "unhandled instruction: " << inst << " @ "
                    << inst.getParent()->getName() << " in "
                    << inst.getParent()->getParent()->getName());
}

/// \brief Returns a symbolic register corresponding to a value
Expr Bv2OpSem::mkSymbReg(const Value &v, OpSemContext &_ctx) {
  return details::ctx(_ctx).mkRegister(v);
}

Expr Bv2OpSem::getSymbReg(const Value &v, const OpSemContext &_ctx) const {
  return const_ctx(_ctx).getRegister(v);
}

/// \brief Returns a concrete value to which a constant evaluates
/// Adapted from llvm::ExecutionEngine
Optional<GenericValue> Bv2OpSem::getConstantValue(const Constant *C) {
  // If its undefined, return the garbage.
  if (isa<UndefValue>(C)) {
    GenericValue Result;
    switch (C->getType()->getTypeID()) {
    default:
      break;
    case Type::IntegerTyID:
    case Type::X86_FP80TyID:
    case Type::FP128TyID:
    case Type::PPC_FP128TyID:
      // Although the value is undefined, we still have to construct an APInt
      // with the correct bit width.
      Result.IntVal = APInt(C->getType()->getPrimitiveSizeInBits(), 0);
      break;
    case Type::StructTyID: {
      // if the whole struct is 'undef' just reserve memory for the value.
      if (StructType *STy = dyn_cast<StructType>(C->getType())) {
        unsigned int elemNum = STy->getNumElements();
        Result.AggregateVal.resize(elemNum);
        for (unsigned int i = 0; i < elemNum; ++i) {
          Type *ElemTy = STy->getElementType(i);
          if (ElemTy->isIntegerTy())
            Result.AggregateVal[i].IntVal =
                APInt(ElemTy->getPrimitiveSizeInBits(), 0);
          else if (ElemTy->isAggregateType()) {
            const Constant *ElemUndef = UndefValue::get(ElemTy);
            Result.AggregateVal[i] = getConstantValue(ElemUndef).getValue();
          }
        }
      }
    } break;
    case Type::VectorTyID:
      // if the whole vector is 'undef' just reserve memory for the value.
      auto *VTy = dyn_cast<VectorType>(C->getType());
      Type *ElemTy = VTy->getElementType();
      unsigned int elemNum = VTy->getNumElements();
      Result.AggregateVal.resize(elemNum);
      if (ElemTy->isIntegerTy())
        for (unsigned int i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].IntVal =
              APInt(ElemTy->getPrimitiveSizeInBits(), 0);
      break;
    }
    return Result;
  }

  // Otherwise, if the value is a ConstantExpr...
  if (const ConstantExpr *CE = dyn_cast<ConstantExpr>(C)) {
    Constant *Op0 = CE->getOperand(0);
    switch (CE->getOpcode()) {
    case Instruction::GetElementPtr: {
      // Compute the index
      GenericValue Result = getConstantValue(Op0).getValue();
      APInt Offset(m_td->getPointerSizeInBits(), 0);
      cast<GEPOperator>(CE)->accumulateConstantOffset(*m_td, Offset);

      char *tmp = (char *)Result.PointerVal;
      Result = PTOGV(tmp + Offset.getSExtValue());
      return Result;
    }
    case Instruction::Trunc: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.trunc(BitWidth);
      return GV;
    }
    case Instruction::ZExt: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.zext(BitWidth);
      return GV;
    }
    case Instruction::SExt: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      GV.IntVal = GV.IntVal.sext(BitWidth);
      return GV;
    }
    case Instruction::FPTrunc: {
      // FIXME long double
      GenericValue GV = getConstantValue(Op0).getValue();
      GV.FloatVal = float(GV.DoubleVal);
      return GV;
    }
    case Instruction::FPExt: {
      // FIXME long double
      GenericValue GV = getConstantValue(Op0).getValue();
      GV.DoubleVal = double(GV.FloatVal);
      return GV;
    }
    case Instruction::UIToFP: {
      GenericValue GV = getConstantValue(Op0).getValue();
      if (CE->getType()->isFloatTy())
        GV.FloatVal = float(GV.IntVal.roundToDouble());
      else if (CE->getType()->isDoubleTy())
        GV.DoubleVal = GV.IntVal.roundToDouble();
      else if (CE->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat::getZero(APFloat::x87DoubleExtended());
        (void)apf.convertFromAPInt(GV.IntVal, false,
                                   APFloat::rmNearestTiesToEven);
        GV.IntVal = apf.bitcastToAPInt();
      }
      return GV;
    }
    case Instruction::SIToFP: {
      GenericValue GV = getConstantValue(Op0).getValue();
      if (CE->getType()->isFloatTy())
        GV.FloatVal = float(GV.IntVal.signedRoundToDouble());
      else if (CE->getType()->isDoubleTy())
        GV.DoubleVal = GV.IntVal.signedRoundToDouble();
      else if (CE->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat::getZero(APFloat::x87DoubleExtended());
        (void)apf.convertFromAPInt(GV.IntVal, true,
                                   APFloat::rmNearestTiesToEven);
        GV.IntVal = apf.bitcastToAPInt();
      }
      return GV;
    }
    case Instruction::FPToUI: // double->APInt conversion handles sign
    case Instruction::FPToSI: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t BitWidth = cast<IntegerType>(CE->getType())->getBitWidth();
      if (Op0->getType()->isFloatTy())
        GV.IntVal = APIntOps::RoundFloatToAPInt(GV.FloatVal, BitWidth);
      else if (Op0->getType()->isDoubleTy())
        GV.IntVal = APIntOps::RoundDoubleToAPInt(GV.DoubleVal, BitWidth);
      else if (Op0->getType()->isX86_FP80Ty()) {
        APFloat apf = APFloat(APFloat::x87DoubleExtended(), GV.IntVal);
        uint64_t v;
        bool ignored;
        (void)apf.convertToInteger(makeMutableArrayRef(v), BitWidth,
                                   CE->getOpcode() == Instruction::FPToSI,
                                   APFloat::rmTowardZero, &ignored);
        GV.IntVal = v; // endian?
      }
      return GV;
    }
    case Instruction::PtrToInt: {
      auto OGV = getConstantValue(Op0);
      if (!OGV.hasValue())
        return llvm::None;
      GenericValue GV = OGV.getValue();

      uint32_t PtrWidth = m_td->getTypeSizeInBits(Op0->getType());
      assert(PtrWidth <= 64 && "Bad pointer width");
      GV.IntVal = APInt(PtrWidth, uintptr_t(GV.PointerVal));
      uint32_t IntWidth = m_td->getTypeSizeInBits(CE->getType());
      GV.IntVal = GV.IntVal.zextOrTrunc(IntWidth);
      return GV;
    }
    case Instruction::IntToPtr: {
      GenericValue GV = getConstantValue(Op0).getValue();
      uint32_t PtrWidth = m_td->getTypeSizeInBits(CE->getType());
      GV.IntVal = GV.IntVal.zextOrTrunc(PtrWidth);
      assert(GV.IntVal.getBitWidth() <= 64 && "Bad pointer width");
      GV.PointerVal = PointerTy(uintptr_t(GV.IntVal.getZExtValue()));
      return GV;
    }
    case Instruction::BitCast: {
      GenericValue GV = getConstantValue(Op0).getValue();
      Type *DestTy = CE->getType();
      switch (Op0->getType()->getTypeID()) {
      default:
        llvm_unreachable("Invalid bitcast operand");
      case Type::IntegerTyID:
        assert(DestTy->isFloatingPointTy() && "invalid bitcast");
        if (DestTy->isFloatTy())
          GV.FloatVal = GV.IntVal.bitsToFloat();
        else if (DestTy->isDoubleTy())
          GV.DoubleVal = GV.IntVal.bitsToDouble();
        break;
      case Type::FloatTyID:
        assert(DestTy->isIntegerTy(32) && "Invalid bitcast");
        GV.IntVal = APInt::floatToBits(GV.FloatVal);
        break;
      case Type::DoubleTyID:
        assert(DestTy->isIntegerTy(64) && "Invalid bitcast");
        GV.IntVal = APInt::doubleToBits(GV.DoubleVal);
        break;
      case Type::PointerTyID:
        assert(DestTy->isPointerTy() && "Invalid bitcast");
        break; // getConstantValue(Op0)  above already converted it
      }
      return GV;
    }
    case Instruction::Add:
    case Instruction::FAdd:
    case Instruction::Sub:
    case Instruction::FSub:
    case Instruction::Mul:
    case Instruction::FMul:
    case Instruction::UDiv:
    case Instruction::SDiv:
    case Instruction::URem:
    case Instruction::SRem:
    case Instruction::And:
    case Instruction::Or:
    case Instruction::Xor: {
      GenericValue LHS = getConstantValue(Op0).getValue();
      GenericValue RHS = getConstantValue(CE->getOperand(1)).getValue();
      GenericValue GV;
      switch (CE->getOperand(0)->getType()->getTypeID()) {
      default:
        llvm_unreachable("Bad add type!");
      case Type::IntegerTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid integer opcode");
        case Instruction::Add:
          GV.IntVal = LHS.IntVal + RHS.IntVal;
          break;
        case Instruction::Sub:
          GV.IntVal = LHS.IntVal - RHS.IntVal;
          break;
        case Instruction::Mul:
          GV.IntVal = LHS.IntVal * RHS.IntVal;
          break;
        case Instruction::UDiv:
          GV.IntVal = LHS.IntVal.udiv(RHS.IntVal);
          break;
        case Instruction::SDiv:
          GV.IntVal = LHS.IntVal.sdiv(RHS.IntVal);
          break;
        case Instruction::URem:
          GV.IntVal = LHS.IntVal.urem(RHS.IntVal);
          break;
        case Instruction::SRem:
          GV.IntVal = LHS.IntVal.srem(RHS.IntVal);
          break;
        case Instruction::And:
          GV.IntVal = LHS.IntVal & RHS.IntVal;
          break;
        case Instruction::Or:
          GV.IntVal = LHS.IntVal | RHS.IntVal;
          break;
        case Instruction::Xor:
          GV.IntVal = LHS.IntVal ^ RHS.IntVal;
          break;
        }
        break;
      case Type::FloatTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid float opcode");
        case Instruction::FAdd:
          GV.FloatVal = LHS.FloatVal + RHS.FloatVal;
          break;
        case Instruction::FSub:
          GV.FloatVal = LHS.FloatVal - RHS.FloatVal;
          break;
        case Instruction::FMul:
          GV.FloatVal = LHS.FloatVal * RHS.FloatVal;
          break;
        case Instruction::FDiv:
          GV.FloatVal = LHS.FloatVal / RHS.FloatVal;
          break;
        case Instruction::FRem:
          GV.FloatVal = std::fmod(LHS.FloatVal, RHS.FloatVal);
          break;
        }
        break;
      case Type::DoubleTyID:
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid double opcode");
        case Instruction::FAdd:
          GV.DoubleVal = LHS.DoubleVal + RHS.DoubleVal;
          break;
        case Instruction::FSub:
          GV.DoubleVal = LHS.DoubleVal - RHS.DoubleVal;
          break;
        case Instruction::FMul:
          GV.DoubleVal = LHS.DoubleVal * RHS.DoubleVal;
          break;
        case Instruction::FDiv:
          GV.DoubleVal = LHS.DoubleVal / RHS.DoubleVal;
          break;
        case Instruction::FRem:
          GV.DoubleVal = std::fmod(LHS.DoubleVal, RHS.DoubleVal);
          break;
        }
        break;
      case Type::X86_FP80TyID:
      case Type::PPC_FP128TyID:
      case Type::FP128TyID: {
        const fltSemantics &Sem =
            CE->getOperand(0)->getType()->getFltSemantics();
        APFloat apfLHS = APFloat(Sem, LHS.IntVal);
        switch (CE->getOpcode()) {
        default:
          llvm_unreachable("Invalid long double opcode");
        case Instruction::FAdd:
          apfLHS.add(APFloat(Sem, RHS.IntVal), APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FSub:
          apfLHS.subtract(APFloat(Sem, RHS.IntVal),
                          APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FMul:
          apfLHS.multiply(APFloat(Sem, RHS.IntVal),
                          APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FDiv:
          apfLHS.divide(APFloat(Sem, RHS.IntVal), APFloat::rmNearestTiesToEven);
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        case Instruction::FRem:
          apfLHS.mod(APFloat(Sem, RHS.IntVal));
          GV.IntVal = apfLHS.bitcastToAPInt();
          break;
        }
      } break;
      }
      return GV;
    }
    default:
      break;
    }

    SmallString<256> Msg;
    raw_svector_ostream OS(Msg);
    OS << "ConstantExpr not handled: " << *CE;
    report_fatal_error(OS.str());
  }

  // Otherwise, we have a simple constant.
  GenericValue Result;
  switch (C->getType()->getTypeID()) {
  case Type::FloatTyID:
    Result.FloatVal = cast<ConstantFP>(C)->getValueAPF().convertToFloat();
    break;
  case Type::DoubleTyID:
    Result.DoubleVal = cast<ConstantFP>(C)->getValueAPF().convertToDouble();
    break;
  case Type::X86_FP80TyID:
  case Type::FP128TyID:
  case Type::PPC_FP128TyID:
    Result.IntVal = cast<ConstantFP>(C)->getValueAPF().bitcastToAPInt();
    break;
  case Type::IntegerTyID:
    Result.IntVal = cast<ConstantInt>(C)->getValue();
    break;
  case Type::PointerTyID:
    if (isa<ConstantPointerNull>(C))
      Result.PointerVal = nullptr;
    else if (const Function *F = dyn_cast<Function>(C))
      // TODO:
      // Result = PTOGV((void*)ctx.getPtrToFunction(*F));
      return llvm::None;
    else if (const GlobalVariable *GV = dyn_cast<GlobalVariable>(C))
      // TODO:
      // Result = PTOGV((void*)ctx.getPtrToGlobal(*GV));
      return llvm::None;
    else
      llvm_unreachable("Unknown constant pointer type!");
    break;
  case Type::VectorTyID: {
    unsigned elemNum;
    Type *ElemTy;
    const ConstantDataVector *CDV = dyn_cast<ConstantDataVector>(C);
    const ConstantVector *CV = dyn_cast<ConstantVector>(C);
    const ConstantAggregateZero *CAZ = dyn_cast<ConstantAggregateZero>(C);

    if (CDV) {
      elemNum = CDV->getNumElements();
      ElemTy = CDV->getElementType();
    } else if (CV || CAZ) {
      VectorType *VTy = dyn_cast<VectorType>(C->getType());
      elemNum = VTy->getNumElements();
      ElemTy = VTy->getElementType();
    } else {
      llvm_unreachable("Unknown constant vector type!");
    }

    Result.AggregateVal.resize(elemNum);
    // Check if vector holds floats.
    if (ElemTy->isFloatTy()) {
      if (CAZ) {
        GenericValue floatZero;
        floatZero.FloatVal = 0.f;
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  floatZero);
        break;
      }
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].FloatVal =
                cast<ConstantFP>(CV->getOperand(i))
                    ->getValueAPF()
                    .convertToFloat();
        break;
      }
      if (CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].FloatVal = CDV->getElementAsFloat(i);

      break;
    }
    // Check if vector holds doubles.
    if (ElemTy->isDoubleTy()) {
      if (CAZ) {
        GenericValue doubleZero;
        doubleZero.DoubleVal = 0.0;
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  doubleZero);
        break;
      }
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].DoubleVal =
                cast<ConstantFP>(CV->getOperand(i))
                    ->getValueAPF()
                    .convertToDouble();
        break;
      }
      if (CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].DoubleVal = CDV->getElementAsDouble(i);

      break;
    }
    // Check if vector holds integers.
    if (ElemTy->isIntegerTy()) {
      if (CAZ) {
        GenericValue intZero;
        intZero.IntVal = APInt(ElemTy->getScalarSizeInBits(), 0ull);
        std::fill(Result.AggregateVal.begin(), Result.AggregateVal.end(),
                  intZero);
        break;
      }
      if (CV) {
        for (unsigned i = 0; i < elemNum; ++i)
          if (!isa<UndefValue>(CV->getOperand(i)))
            Result.AggregateVal[i].IntVal =
                cast<ConstantInt>(CV->getOperand(i))->getValue();
          else {
            Result.AggregateVal[i].IntVal = APInt(
                CV->getOperand(i)->getType()->getPrimitiveSizeInBits(), 0);
          }
        break;
      }
      if (CDV)
        for (unsigned i = 0; i < elemNum; ++i)
          Result.AggregateVal[i].IntVal =
              APInt(CDV->getElementType()->getPrimitiveSizeInBits(),
                    CDV->getElementAsInteger(i));

      break;
    }
    llvm_unreachable("Unknown constant pointer type!");
  } break;

  default:
    SmallString<256> Msg;
    raw_svector_ostream OS(Msg);
    OS << "ERROR: Constant unimplemented for type: " << *C->getType();
    report_fatal_error(OS.str());
  }

  return Result;
}

void Bv2OpSem::execEdg(const BasicBlock &src, const BasicBlock &dst,
                       details::Bv2OpSemContext &ctx) {
  exec(src, ctx.act(trueE));
  execBr(src, dst, ctx);
  execPhi(dst, src, ctx);

  // an edge into a basic block that does not return includes the block itself
  const TerminatorInst *term = dst.getTerminator();
  if (term && isa<const UnreachableInst>(term))
    exec(dst, ctx);
}

void Bv2OpSem::execBr(const BasicBlock &src, const BasicBlock &dst,
                      details::Bv2OpSemContext &ctx) {
  ctx.onBasicBlockEntry(src);
  ctx.setInstruction(*src.getTerminator());
  intraBr(ctx, dst);
}

} // namespace seahorn

namespace seahorn {
namespace details {
/// \brief Unwraps a context
seahorn::details::Bv2OpSemContext &ctx(OpSemContext &_ctx) {
  return static_cast<seahorn::details::Bv2OpSemContext &>(_ctx);
}
} // namespace details
} // namespace seahorn
namespace {
// \brief Unwraps a const context
const seahorn::details::Bv2OpSemContext &const_ctx(const OpSemContext &_ctx) {
  return static_cast<const seahorn::details::Bv2OpSemContext &>(_ctx);
}
} // namespace
