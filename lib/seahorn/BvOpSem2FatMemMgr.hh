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

namespace seahorn {
namespace details {

static const unsigned int g_slotBitWidth = 64;
static const unsigned int g_slotByteWidth = g_slotBitWidth / 8;

// TODO: remove these vars
// static const unsigned int g_undefSlot0 = 0xDEF0;
// static const unsigned int g_undefSlot1 = 0xDEF1;

/// \brief provides Fat pointers and Fat memory to store them
template <class T> class FatMemManagerCore : public MemManagerCore {
  static unsigned g_FatMemSlots;

private:
  /// \brief Memory manager for raw pointers
  T m_main;
  std::vector<RawMemManager> m_slots;

public:
  /// Right now everything is an expression. In the future, we might have
  /// other types for PtrTy, such as a tuple of expressions
  using MainPtrTy = typename T::PtrTy;
  using RawPtrTy = OpSemMemManager::PtrTy;
  using MainMemValTy = typename T::MemValTy;
  using RawMemValTy = OpSemMemManager::MemValTy;
  using AnyPtrTy = Expr;
  using AnyMemValTy = Expr;

  /// \brief Source of unique identifiers (currently inc. counter)
  mutable unsigned m_id;

  llvm::Twine m_fatMemBaseName;

  /// PtrTy representation for this manager
  ///
  /// Currently internal representation is just an Expr
  struct PtrTyImpl {
    Expr m_v;

    explicit PtrTyImpl(llvm::SmallVector<AnyPtrTy, 8> &&slots) {
      assert(slots.size() == g_FatMemSlots + 1);
      for (auto e : slots) {
        assert(e);
      }
      m_v = strct::mk(std::move(slots));
    }

    explicit PtrTyImpl(llvm::SmallVector<AnyPtrTy, 8> &slots) {
      assert(slots.size() == g_FatMemSlots + 1);
      for (auto e : slots) {
        assert(e);
      }
      m_v = strct::mk(slots);
    }

    explicit PtrTyImpl(const Expr &e) {
      // Our base is a struct of three exprs
      assert(strct::isStructVal(e));
      assert(e->arity() == g_FatMemSlots + 1);
      for (unsigned i = 0, sz = e->arity(); i < sz; i++) {
        assert(e->arg(i));
      }
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    MainPtrTy getMain() { return strct::extractVal(m_v, 0); }

    MainPtrTy getRaw() { return getMain(); }

    Expr getSlot(unsigned idx) {
      assert(idx < g_FatMemSlots + 1);
      auto e = strct::extractVal(m_v, idx);
      assert(e); // e is not null
      return e;
    }
  };

  struct MemValTyImpl {
    Expr m_v;

    explicit MemValTyImpl(llvm::SmallVector<AnyMemValTy, 8> &&vals) {
      assert(vals.size() == g_FatMemSlots + 1);
      for (auto e : vals) {
        assert(e);
      }
      // TODO: add back isStructVal check
      m_v = strct::mk(std::move(vals));
    }

    explicit MemValTyImpl(llvm::SmallVector<AnyMemValTy, 8> &vals) {
      assert(vals.size() == g_FatMemSlots + 1);
      for (auto e : vals) {
        assert(e);
      }

      // TODO: add back isStructVal check
      m_v = strct::mk(vals);
    }

    explicit MemValTyImpl(const Expr &e) {
      // Our base is Expr() or a struct of three exprs
      assert(!e || strct::isStructVal(e));
      for (unsigned i = 0; i < g_FatMemSlots; i++) {
        assert(!e || !strct::isStructVal(e->arg(i + 1)));
      }
      if (e) {
        assert(e->arity() == g_FatMemSlots + 1);
        for (unsigned i = 0, sz = e->arity(); i < sz; i++) {
          assert(e->arg(i));
        }
      }
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    MainMemValTy getMain() { return !m_v ? m_v : strct::extractVal(m_v, 0); }

    MainMemValTy getRaw() { return getMain(); }

    Expr getSlot(unsigned idx) {
      assert(idx < g_FatMemSlots + 1);
      auto e = strct::extractVal(m_v, idx);
      assert(e); // e is not null
      return e;
    }
  };

  using FatMemTag = MemoryFeatures::FatMem_tag;
  using TrackingTag = typename T::TrackingTag;
  using WideMemTag = typename T::WideMemTag;

  using MemValTy = MemValTyImpl;
  using PtrTy = PtrTyImpl;

  using MainPtrSortTy = typename T::PtrSortTy;
  using MainMemSortTy = typename T::MemSortTy;
  using MemRegTy = OpSemMemManager::MemRegTy;
  using AnyPtrSortTy = Expr;
  using AnyMemSortTy = Expr;

  // TODO: change all slot0,1 methods to return these types for easier
  // reading
  using Slot0ValTy = Expr;
  using Slot1ValTy = Expr;

  struct PtrSortTyImpl {
    Expr m_ptr_sort;

    explicit PtrSortTyImpl(llvm::SmallVector<AnyPtrSortTy, 8> &&ptrSorts) {
      assert(ptrSorts.size() == g_FatMemSlots + 1);
      for (auto e : ptrSorts) {
        assert(e);
      }
      m_ptr_sort = sort::structTy(std::move(ptrSorts));
    }

    explicit PtrSortTyImpl(llvm::SmallVector<AnyPtrSortTy, 8> &ptrSorts) {
      assert(ptrSorts.size() == g_FatMemSlots + 1);
      for (auto e : ptrSorts) {
        assert(e);
      }
      m_ptr_sort = sort::structTy(std::move(ptrSorts));
    }

    Expr v() const { return m_ptr_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    MainPtrSortTy getBaseSort() { return m_ptr_sort->arg(0); }
  };

  struct MemSortTyImpl {
    Expr m_mem_sort;

    explicit MemSortTyImpl(llvm::SmallVector<AnyMemSortTy, 8> &&memSorts) {
      assert(memSorts.size() == g_FatMemSlots + 1);
      for (auto e : memSorts) {
        assert(e);
      }
      m_mem_sort = sort::structTy(std::move(memSorts));
    }

    explicit MemSortTyImpl(llvm::SmallVector<AnyMemSortTy, 8> &memSorts) {
      assert(memSorts.size() == g_FatMemSlots + 1);
      for (auto e : memSorts) {
        assert(e);
      }
      m_mem_sort = sort::structTy(memSorts);
    }

    Expr v() const { return m_mem_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }
  };

  using PtrSortTy = PtrSortTyImpl;
  using MemSortTy = MemSortTyImpl;

  /// \brief Converts a raw ptr to fat ptr with default value for fat
  PtrTy mkFatPtr(MainPtrTy mainPtr) const;

  /// \brief Assembles a fat ptr from parts
  PtrTy mkFatPtr(llvm::SmallVector<AnyPtrTy, 8> slots) const;

  /// \brief Update a given fat pointer with a "main" address value
  PtrTy updateFatPtr(MainPtrTy mainPtr, PtrTy fat) const;

  /// \brief Extracts a "main" pointer out of a fat pointer
  MainPtrTy mkMainPtr(PtrTy fatPtr) const;

  /// \brief Extracts a "main" memory value from a fat memory value
  MainMemValTy mkMainMem(MemValTy fatMem) const;

  RawMemValTy mkSlot0Mem(MemValTy fatMem) const;

  RawMemValTy mkSlot1Mem(MemValTy fatMem) const;

  /// \brief Creates a fat memory value from raw memory with given values
  /// for fat
  MemValTy mkFatMem(llvm::SmallVector<AnyMemValTy, 8> vals) const;

public:
  FatMemManagerCore(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                    unsigned wordSz, bool useLambdas = false);

  ~FatMemManagerCore() = default;

  PtrSortTy ptrSort() const;

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  PtrTy salloc(unsigned bytes, uint32_t align);

  /// \brief Allocates memory on the stack and returns a pointer to it
  PtrTy salloc(Expr elmts, unsigned typeSz, uint32_t align);

  /// \brief Returns a pointer value for a given stack allocation
  PtrTy mkStackPtr(unsigned offset);

  /// \brief Pointer to start of the heap
  PtrTy brk0Ptr();

  /// \brief Allocates memory on the heap and returns a pointer to it
  PtrTy halloc(unsigned _bytes, uint32_t align);

  /// \brief Allocates memory on the heap and returns pointer to it
  PtrTy halloc(Expr bytes, uint32_t align);

  /// \brief Allocates memory in global (data/bss) segment for given global
  PtrTy galloc(const GlobalVariable &gv, uint32_t align);

  /// \brief Allocates memory in code segment for the code of a given
  /// function
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
  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const;

  /// \brief Returns sort of a pointer register for a function pointer
  PtrSortTy mkPtrRegisterSort(const Function &fn) const;

  /// \brief Returns sort of a pointer register for a global pointer
  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const;

  /// \brief Returns sort of memory-holding register for an instruction
  MemSortTy mkMemRegisterSort(const Instruction &inst) const;

  /// \brief Returns a fresh aligned pointer value
  PtrTy freshPtr();

  /// \brief Returns a null ptr
  PtrTy nullPtr() const;

  /// \brief Fixes the type of a havoced value to mach the representation
  /// used by mem repr.
  ///
  /// \param sort
  /// \param val
  /// \return the coerced value.
  Expr coerce(Expr sort, Expr val);

  /// \brief Loads an integer of a given size from 'raw' memory register
  ///
  /// \param[in] ptr pointer being accessed
  /// \param[in] mem memory value into which \p ptr points
  /// \param[in] byteSz size of the integer in bytes
  /// \param[in] align known alignment of \p ptr
  /// \return symbolic value of the read integer
  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz, uint64_t align);

  /// \brief Loads a pointer stored in memory
  /// \sa loadIntFromMem
  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned byteSz,
                       uint64_t align);

  /// \brief Pointer addition with numeric offset
  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const;

  /// \brief Pointer addition with symbolic offset
  PtrTy ptrAdd(PtrTy ptr, Expr offset) const;

  /// \brief Stores an integer into memory
  ///
  /// Returns an expression describing the state of memory in \c memReadReg
  /// after the store
  /// \sa loadIntFromMem
  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align);

  /// \brief Stores a pointer into memory
  /// \sa storeIntToMem
  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem, unsigned byteSz,
                         uint64_t align);

  /// \brief Returns an expression corresponding to a load from memory
  ///
  /// \param[in] ptr is the pointer being dereferenced
  /// \param[in] memReg is the memory register being read
  /// \param[in] ty is the type of value being loaded
  /// \param[in] align is the known alignment of the load
  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const llvm::Type &ty,
                        uint64_t align);

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn,
                           const llvm::Type &ty, uint32_t align);

  /// \brief Executes symbolic memset with a concrete length
  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned len, MemValTy mem,
                  uint32_t align);

  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem, uint32_t align);

  /// \brief Executes symbolic memcpy with concrete length
  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align);

  /// \brief Executes symbolic memcpy with concrete length
  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align);

  /// \brief Executes symbolic memcpy from physical memory with concrete
  /// length
  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned len, MemValTy mem,
                   uint32_t align = 0);

  /// \brief Executes inttoptr conversion
  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const;

  /// \brief Executes ptrtoint conversion. This only converts the raw ptr to
  /// int.
  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const;

  Expr ptrEq(PtrTy p1, PtrTy p2) const;
  Expr ptrUlt(PtrTy p1, PtrTy p2) const;
  Expr ptrSlt(PtrTy p1, PtrTy p2) const;
  Expr ptrUle(PtrTy p1, PtrTy p2) const;
  Expr ptrSle(PtrTy p1, PtrTy p2) const;
  Expr ptrUgt(PtrTy p1, PtrTy p2) const;
  Expr ptrSgt(PtrTy p1, PtrTy p2) const;
  Expr ptrUge(PtrTy p1, PtrTy p2) const;
  Expr ptrSge(PtrTy p1, PtrTy p2) const;
  Expr ptrNe(PtrTy p1, PtrTy p2) const;
  Expr ptrSub(PtrTy p1, PtrTy p2) const;

  /// \brief Computes a pointer corresponding to the gep instruction
  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const;

  /// \brief Called when a function is entered for the first time
  void onFunctionEntry(const Function &fn);

  /// \brief Called when a module entered for the first time
  void onModuleEntry(const Module &M);

  /// \brief Debug helper
  void dumpGlobalsMap();

  std::pair<char *, unsigned>
  getGlobalVariableInitValue(const llvm::GlobalVariable &gv);

  MemValTy zeroedMemory() const;

  /// \brief get fat data in ith fat slot.
  Expr getFatData(PtrTy p, unsigned SlotIdx);

  PtrTy setFatData(PtrTy p, unsigned slotIdx, Expr data);

  RawPtrTy getAddressable(PtrTy p) const;

  bool isPtrTyVal(Expr e) const;

  bool isMemVal(Expr e) const;

  Expr isMetadataSet(MetadataKind kind, PtrTy ptr, MemValTy mem);

  MemValTy memsetMetadata(MetadataKind kind, PtrTy ptr, unsigned int len,
                          MemValTy memIn, unsigned int val);

  MemValTy memsetMetadata(MetadataKind kind, PtrTy ptr, Expr len,
                          MemValTy memIn, unsigned int val);

  Expr getMetadata(MetadataKind kind, PtrTy ptr, MemValTy memIn,
                   unsigned int byteSz);

  unsigned int getMetadataMemWordSzInBits();

  size_t getNumOfMetadataSlots();
  MemValTy setMetadata(MetadataKind kind, PtrTy ptr, MemValTy mem, Expr val);

  Expr isDereferenceable(PtrTy p, Expr byteSz);
};
OpSemMemManager *mkFatMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas);

// FatMemManager with ExtraWide and Tracking components
OpSemMemManager *mkFatEWWTManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                  unsigned ptrSz, unsigned wordSz,
                                  bool useLambdas);
using FatEWWTMemManager =
    OpSemMemManagerMixin<FatMemManagerCore<EWWTMemManager>>;
// FatMemManager with ExtraWide and Tracking components
OpSemMemManager *mkFatEWWManager(Bv2OpSem &sem, Bv2OpSemContext &ctx,
                                 unsigned ptrSz, unsigned wordSz,
                                 bool useLambdas);
using FatEWWMemManager = OpSemMemManagerMixin<FatMemManagerCore<EWWMemManager>>;
} // namespace details
} // namespace seahorn
