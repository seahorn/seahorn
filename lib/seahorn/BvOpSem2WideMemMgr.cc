#include "BvOpSem2Context.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "BvOpSem2WideMemManagerMixin.hh"

#include "seahorn/Expr/ExprOpStruct.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

static const unsigned int g_slotBitWidth = 64;
static const unsigned int g_slotByteWidth = g_slotBitWidth / 8;

static const unsigned int g_uninit = 0xDEADBEEF;
static const unsigned int g_num_slots = 2;

namespace seahorn {
namespace details {
class WideMemManager : public OpSemMemManagerBase {

  /// \brief Knows the memory representation and how to access it
  std::unique_ptr<OpSemMemRepr> m_memRepr;

  /// \brief Base name for non-deterministic pointer
  Expr m_freshPtrName;

  /// \brief Register that contains the value of the stack pointer on
  /// function entry
  Expr m_sp0;

  /// \brief Source of unique identifiers
  mutable unsigned m_id;

  const Expr m_uninit_size;

  /// \brief Memory manager for raw pointers
  RawMemManager m_main;
  RawMemManager m_size;

public:
  using RawPtrTy = OpSemMemManager::PtrTy;
  using RawMemValTy = OpSemMemManager::MemValTy;
  using RawPtrSortTy = OpSemMemManager::PtrSortTy;
  using RawMemSortTy = OpSemMemManager::MemSortTy;
  using MemRegTy = OpSemMemManager::MemRegTy;

  // size = size in bits
  struct PtrTyImpl {
    Expr m_v;

    PtrTyImpl(RawPtrTy &&ptr, Expr &&size) {
      m_v = strct::mk(std::move(ptr), std::move(size));
    }

    PtrTyImpl(const RawPtrTy &ptr, const Expr &size) {
      m_v = strct::mk(ptr, size);
    }

    explicit PtrTyImpl(const Expr &e) {
      // Our ptr is a struct of two exprs
      assert(strct::isStructVal(e));
      assert(e->arity() == g_num_slots);
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawPtrTy getRaw() { return strct::extractVal(m_v, 0); }

    Expr getSize() { return strct::extractVal(m_v, 1); }
  };

  struct MemValTyImpl {
    Expr m_v;

    MemValTyImpl(RawMemValTy &&raw_val, Expr &&size_val) {
      m_v = strct::mk(std::move(raw_val), std::move(size_val));
    }

    MemValTyImpl(const RawPtrTy &raw_val, const Expr &size_val) {
      m_v = strct::mk(raw_val, size_val);
    }

    explicit MemValTyImpl(const Expr &e) {
      // Our ptr is a struct of two exprs
      assert(strct::isStructVal(e));
      assert(e->arity() == g_num_slots);
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawMemValTy getRaw() { return strct::extractVal(m_v, 0); }

    RawMemValTy getSize() { return strct::extractVal(m_v, 1); }
  };

  struct PtrSortTyImpl {
    Expr m_ptr_sort;

    PtrSortTyImpl(RawPtrSortTy &&ptr_sort, Expr &&size_sort) {
      m_ptr_sort = sort::structTy(std::move(ptr_sort), std::move(size_sort));
    }

    PtrSortTyImpl(const RawPtrSortTy &ptr_sort, const Expr &size_sort) {
      m_ptr_sort = sort::structTy(ptr_sort, size_sort);
    }

    Expr v() const { return m_ptr_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawPtrSortTy getRawSort() { return m_ptr_sort->arg(0); }
  };

  struct MemSortTyImpl {
    Expr m_mem_sort;

    MemSortTyImpl(RawMemSortTy &&mem_sort, Expr &&size_sort) {
      m_mem_sort = sort::structTy(std::move(mem_sort), std::move(size_sort));
    }

    MemSortTyImpl(const RawMemSortTy &mem_sort, const Expr &size_sort) {
      m_mem_sort = sort::structTy(mem_sort, size_sort);
    }

    Expr v() const { return m_mem_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }
  };

  using PtrTy = PtrTyImpl;
  using PtrSortTy = PtrSortTyImpl;
  using MemValTy = MemValTyImpl;
  using MemSortTy = MemSortTyImpl;

  /// \brief A null pointer expression (cache)
  PtrTy m_nullPtr;

  WideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                 unsigned wordSz, bool useLambdas = false);

  ~WideMemManager() = default;

  Expr bytesToSlotExpr(unsigned bytes) {
    return m_ctx.alu().si(bytes, g_slotBitWidth);
  }

  PtrSortTy ptrSort() const {
    return PtrSortTy(m_main.ptrSort(), m_ctx.alu().intTy(g_slotBitWidth));
  }

  PtrTy salloc(unsigned int bytes, uint32_t align) {
    assert(isa<AllocaInst>(m_ctx.getCurrentInst()));
    align = std::max(align, m_alignment);
    auto region = m_main.getMAllocator().salloc(bytes, align);
    assert(region.second > region.first);
    // The size is min(alloc_size, requested_size)
    return PtrTy(
        mkStackPtr(region.second).getRaw(),
        bytesToSlotExpr(std::min(region.second - region.first, bytes)));
  }

  PtrTy salloc(Expr elmts, unsigned int typeSz, uint32_t align) {
    align = std::max(align, m_alignment);

    // -- compute number of bytes needed
    Expr bytes = elmts;
    if (typeSz > 1) {
      // TODO: factor out multiplication and number creation
      bytes = m_ctx.alu().doMul(bytes, m_ctx.alu().si(typeSz, ptrSzInBits()),
                                ptrSzInBits());
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
                 m_ctx.alu().si(region.first - region.second, g_slotBitWidth));
  }

  PtrTy mkStackPtr(unsigned int offset) {
    return PtrTy(m_main.mkStackPtr(offset), m_uninit_size);
  }

  PtrTy brk0Ptr() { return PtrTy(m_main.brk0Ptr(), m_uninit_size); }

  PtrTy halloc(unsigned int _bytes, uint32_t align) {
    PtrTy res = freshPtr();
    LOG("opsem", WARN << "halloc() not implemented!\n");
    return res;
  }

  PtrTy halloc(Expr bytes, uint32_t align) {
    PtrTy res = freshPtr();
    LOG("opsem", WARN << "halloc() not implemented!\n");
    return res;
  }

  PtrTy galloc(const GlobalVariable &gv, uint32_t align) {
    uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
    auto range =
        m_main.getMAllocator().galloc(gv, gvSz, std::max(align, m_alignment));
    return PtrTy(m_ctx.alu().si(range.first, ptrSzInBits()),
                 bytesToSlotExpr(range.second - range.first));
  }

  PtrTy falloc(const Function &fn) {
    auto range = m_main.getMAllocator().falloc(fn, m_alignment);
    return PtrTy(m_ctx.alu().si(range.first, ptrSzInBits()),
                 bytesToSlotExpr(range.second - range.first));
  }

  // TODO: What is the right size to return here?
  PtrTy getPtrToFunction(const Function &F) {
    auto rawPtr = m_ctx.alu().si(
        m_main.getMAllocator().getFunctionAddrAndSize(F, m_alignment).first,
        ptrSzInBits());
    auto size = m_ctx.alu().si(
        m_main.getMAllocator().getFunctionAddrAndSize(F, m_alignment).second,
        g_slotBitWidth);
    return PtrTy(rawPtr, size);
  }

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv) {
    // TODO: Add a map of ptr to AllocInfo in allocator so that given any ptr,
    // we can get size of allocation.
    uint64_t gvSz = m_sem.getTD().getTypeAllocSize(gv.getValueType());
    return PtrTy(m_ctx.alu().si(m_main.getMAllocator().getGlobalVariableAddr(
                                    gv, gvSz, m_alignment),
                                ptrSzInBits()),
                 bytesToSlotExpr(gvSz));
  }

  void initGlobalVariable(const GlobalVariable &gv) const {
    m_main.initGlobalVariable(gv);
  }

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const {
    m_size.mkAlignedPtr(name, align);
    return PtrTy(m_main.mkAlignedPtr(name, align), m_uninit_size);
  }

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const {
    return PtrSortTy(m_main.mkPtrRegisterSort(inst),
                     m_ctx.alu().intTy(g_slotBitWidth));
  }

  PtrSortTy mkPtrRegisterSort(const Function &fn) const { return ptrSort(); }

  /// \brief Returns sort of a pointer register for a global pointer
  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const {
    return ptrSort();
  }

  MemSortTy mkMemRegisterSort(const Instruction &inst) const {
    RawMemSortTy mainSort = m_main.mkMemRegisterSort(inst);
    RawMemSortTy sizeSort = m_size.mkMemRegisterSort(inst);
    return MemSortTy(mainSort, sizeSort);
  }

  PtrTy freshPtr() {
    Expr name = op::variant::variant(m_id++, m_freshPtrName);
    return mkAlignedPtr(name, m_alignment);
  }

  PtrTy nullPtr() const { return m_nullPtr; }

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

  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const {
    if (_offset == 0)
      return ptr;
    expr::mpz_class offset((signed long)_offset);
    auto address = m_ctx.alu().doAdd(
        ptr.getRaw(), m_ctx.alu().si(offset, ptrSzInBits()), ptrSzInBits());
    Expr new_size;
    // do concrete computation if possible.
    if (m_ctx.alu().isNum(ptr.getSize())) {
      signed conc_size = m_ctx.alu().toNum(ptr.getSize()).get_si();
      new_size = m_ctx.alu().si(conc_size - _offset, g_slotBitWidth);
    } else {
      new_size = m_ctx.alu().doSub(ptr.getSize(),
                                   m_ctx.alu().si(offset, g_slotBitWidth),
                                   g_slotBitWidth);
    }
    return PtrTy(address, new_size);
  }

  PtrTy ptrAdd(PtrTy ptr, Expr offset) const {
    if (m_ctx.alu().isNum(offset)) {
      expr::mpz_class _offset = m_ctx.alu().toNum(offset);
      return ptrAdd(ptr, _offset.get_si());
    }
    // TODO: What is the bitwidth of offset here?
    auto address = m_ctx.alu().doAdd(ptr.getRaw(), offset, ptrSzInBits());
    auto new_size = m_ctx.alu().doSub(ptr.getSize(), offset, g_slotBitWidth);

    return PtrTy(address, new_size);
  }

  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                      uint64_t align) {
    return m_main.loadIntFromMem(ptr.getRaw(), mem.getRaw(), byteSz, align);
  }

  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                       uint64_t align) {
    RawMemValTy rawVal =
        m_main.loadPtrFromMem(ptr.getRaw(), mem.getRaw(), byteSz, align);
    RawMemValTy sizeVal = m_size.loadIntFromMem(ptr.getRaw(), mem.getSize(),
                                                g_slotByteWidth, align);
    return PtrTy(rawVal, sizeVal);
  }

  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align) {
    if (strct::isStructVal(_val)) {
      // LLVM can sometimes cast a ptr to int without ptrtoint
      // In such cases our VM will interpret the int rightly as a struct
      if (_val->arity() == g_num_slots) {
        LOG("opsem", WARN << "fixing: int is actually a struct, unpacking "
                             "before store\n");
        auto raw_val = strct::extractVal(_val, 0);
        auto size_val = strct::extractVal(_val, 1);
        return MemValTy(m_main.storeIntToMem(raw_val, ptr.getRaw(),
                                             mem.getRaw(), byteSz, align),
                        m_size.storeIntToMem(size_val, ptr.getRaw(),
                                             mem.getSize(), g_slotByteWidth,
                                             align));

      } else {
        LOG("opsem", ERR << "fixing: int is a struct: expected arity "
                         << g_num_slots << " but got " << _val->arity()
                         << ".\n");
      }
    }
    return MemValTy(
        m_main.storeIntToMem(_val, ptr.getRaw(), mem.getRaw(), byteSz, align),
        mem.getSize());
  }

  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align) {
    RawMemValTy main = m_main.storePtrToMem(val.getRaw(), ptr.getRaw(),
                                            mem.getRaw(), byteSz, align);
    RawMemValTy size = m_size.storeIntToMem(
        val.getSize(), ptr.getRaw(), mem.getSize(), g_slotByteWidth, align);
    return MemValTy(main, size);
  }

  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const Type &ty,
                        uint64_t align) {
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

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn, const Type &ty,
                           uint32_t align) {
    assert(ptr.v());
    Expr val = _val;
    const unsigned byteSz =
        m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
    ExprFactory &efac = ptr.v()->efac();
    // init memval to a default value
    MemValTy res(m_ctx.alu().si(0UL, wordSzInBits()), m_uninit_size);
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

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned int len, MemValTy mem,
                  uint32_t align) {
    return MemValTy(m_main.MemSet(ptr.getRaw(), _val, len, mem.getRaw(), align),
                    mem.getSize());
  }

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned int len,
                  MemValTy memTrsfrRead, uint32_t align) {
    return MemValTy(m_main.MemCpy(dPtr.getRaw(), sPtr.getRaw(), len,
                                  memTrsfrRead.getRaw(), align),
                    m_size.MemCpy(dPtr.getRaw(), sPtr.getRaw(), len,
                                  memTrsfrRead.getSize(), align));
  }

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned int len, MemValTy mem,
                   uint32_t align) {
    return MemValTy(
        m_main.MemFill(dPtr.getRaw(), sPtr, len, mem.getRaw(), align),
        mem.getSize());
  }

  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const {
    return PtrTy(m_main.inttoptr(intVal, intTy, ptrTy), m_uninit_size);
  }

  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const {
    return m_main.ptrtoint(ptr.getRaw(), ptrTy, intTy);
  }

  /// \brief Checks if two pointers are equal considering only the raw part.
  Expr ptrEq(PtrTy p1, PtrTy p2) const {
    return m_main.ptrEq(p1.getRaw(), p2.getRaw());
  }

  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const {
    RawPtrTy rawPtr = m_main.gep(ptr.getRaw(), it, end);
    // offset bitwidth is ptrSz
    auto offset = m_main.ptrSub(rawPtr, ptr.getRaw());
    auto new_size = m_ctx.alu().doSub(ptr.getSize(), castPtrSzToSlotSz(offset),
                                      g_slotBitWidth);

    return PtrTy(rawPtr, new_size);
  }

  void onFunctionEntry(const Function &fn) { m_main.onFunctionEntry(fn); }

  void onModuleEntry(const Module &M) { m_main.onModuleEntry(M); }

  void dumpGlobalsMap() { m_main.dumpGlobalsMap(); }

  std::pair<char *, unsigned int>
  getGlobalVariableInitValue(const GlobalVariable &gv) {
    return m_main.getGlobalVariableInitValue(gv);
  }

  MemValTy zeroedMemory() const {
    return MemValTy(m_main.zeroedMemory(), m_size.zeroedMemory());
  }

  Expr isDereferenceable(PtrTy p, Expr byteSz) {
    // size should be >= byteSz
    if (m_ctx.alu().isNum(byteSz) && m_ctx.alu().isNum(p.getSize())) {
      signed numBytes = m_ctx.alu().toNum(byteSz).get_si();
      signed conc_size = m_ctx.alu().toNum(p.getSize()).get_si();
      return conc_size >= numBytes ? m_ctx.alu().getTrue()
                                   : m_ctx.alu().getFalse();
    } else {
      return m_ctx.alu().doSge(p.getSize(), castWordSzToSlotSz(byteSz),
                               g_slotBitWidth);
    }
  }

  RawPtrTy getAddressable(PtrTy p) const { return p.getRaw(); }

  Expr getSize(PtrTy p) const { return p.getSize(); }

  const OpSemMemManager &getMainMemMgr() const { return m_main; }

  Expr castPtrSzToSlotSz(const Expr val) const {
    if (ptrSzInBits() == g_slotBitWidth) {
      return val;
    } else if (g_slotBitWidth > ptrSzInBits()) {
      return m_ctx.alu().doSext(val, g_slotBitWidth, ptrSzInBits());
    } else {
      LOG("opsem", WARN << "widemem: Casting ptrSz to slotSz - information may "
                           "be lost!\n");
      return m_ctx.alu().doTrunc(val, g_slotBitWidth);
    }
  }

  Expr castWordSzToSlotSz(const Expr val) const {
    if (wordSzInBits() == g_slotBitWidth) {
      return val;
    } else if (g_slotBitWidth > wordSzInBits()) {
      return m_ctx.alu().doSext(val, g_slotBitWidth, wordSzInBits());
    } else {
      LOG("opsem",
          WARN << "widemem: Casting wordSz to slotSz - information may "
                  "be lost!\n");
      return m_ctx.alu().doTrunc(val, g_slotBitWidth);
    }
  }
};

WideMemManager::WideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                               unsigned ptrSz, unsigned wordSz, bool useLambdas)
    : OpSemMemManagerBase(
          sem, ctx, ptrSz, wordSz,
          false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_size(sem, ctx, ptrSz, g_slotByteWidth, useLambdas, true),
      m_uninit_size(m_ctx.alu().si(g_uninit, g_slotBitWidth)),
      m_nullPtr(PtrTy(m_main.nullPtr(), m_uninit_size)) {}

OpSemMemManager *mkWideMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                  unsigned ptrSz, unsigned wordSz,
                                  bool useLambdas) {
  return new OpSemWideMemManagerMixin<WideMemManager>(sem, ctx, ptrSz, wordSz,
                                                      useLambdas);
}
} // namespace details
} // namespace seahorn
