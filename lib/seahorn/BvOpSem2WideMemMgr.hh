#pragma once

#include "BvOpSem2Context.hh"
#include "BvOpSem2MemManagerMixin.hh"
#include "BvOpSem2RawMemMgr.hh"

namespace seahorn {
namespace details {

class WideMemManager : public MemManagerCore {

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
  // setting TrackingTag to int disqualifies this class as having tracking
  using TrackingTag = int;
  using FatMemTag = int;

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

  Expr bytesToSlotExpr(unsigned bytes);

  PtrSortTy ptrSort() const;

  PtrTy salloc(unsigned int bytes, uint32_t align);

  PtrTy salloc(Expr elmts, unsigned int typeSz, uint32_t align);

  PtrTy mkStackPtr(unsigned int offset);

  PtrTy brk0Ptr();

  PtrTy halloc(unsigned int _bytes, uint32_t align);

  PtrTy halloc(Expr bytes, uint32_t align);

  PtrTy galloc(const GlobalVariable &gv, uint32_t align);

  PtrTy falloc(const Function &fn);

  // TODO: What is the right size to return here?
  PtrTy getPtrToFunction(const Function &F);

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv);

  void initGlobalVariable(const GlobalVariable &gv) const;

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const;

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const;

  PtrSortTy mkPtrRegisterSort(const Function &fn) const;

  /// \brief Returns sort of a pointer register for a global pointer
  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const;

  MemSortTy mkMemRegisterSort(const Instruction &inst) const;

  PtrTy freshPtr();

  PtrTy nullPtr() const { return m_nullPtr; }

  Expr coerce(Expr sort, Expr val);

  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const;

  PtrTy ptrAdd(PtrTy ptr, Expr offset) const;

  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                      uint64_t align);

  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                       uint64_t align);

  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align);

  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align);

  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const Type &ty,
                        uint64_t align);

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn, const Type &ty,
                           uint32_t align);

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned int len, MemValTy mem,
                  uint32_t align);

  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem, uint32_t align);

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned int len,
                  MemValTy memTrsfrRead, MemValTy memRead, uint32_t align);

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align);

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned int len, MemValTy mem,
                   uint32_t align);

  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const;

  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const;

  /// \brief Checks if two pointers are equal considering only the raw part.
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

  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const;

  void onFunctionEntry(const Function &fn);

  void onModuleEntry(const Module &M);

  void dumpGlobalsMap();

  std::pair<char *, unsigned int>
  getGlobalVariableInitValue(const GlobalVariable &gv);

  MemValTy zeroedMemory() const;

  Expr isDereferenceable(PtrTy p, Expr byteSz);

  RawPtrTy getAddressable(PtrTy p) const;

  bool isPtrTyVal(Expr e) const;

  Expr getSize(PtrTy p);

  const OpSemMemManager &getMainMemMgr() const;

  Expr castPtrSzToSlotSz(const Expr val) const;

  Expr castWordSzToSlotSz(const Expr val) const;
};

} // namespace details
} // namespace seahorn
