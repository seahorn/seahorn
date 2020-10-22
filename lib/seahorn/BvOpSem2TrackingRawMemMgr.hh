#pragma once

#include "BvOpSem2Context.hh"
#include "BvOpSem2RawMemMgr.hh"

#include "seahorn/Expr/ExprOpStruct.hh"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/Support/MathExtras.h"
#include <bits/stdint-uintn.h>

namespace seahorn {
namespace details {

// This memory manager adds a metadata memory(backed by raw memory) sitting side
// by side to conventional memory(backed by raw memory). The word size for
// conventional memory can be greater than metadata memory.
//
// Currently this implementation has a metadata memory word size of 1 byte.
// For every byte written to conventional memory, we set the corresponding
// metadata memory address to value 1.
class TrackingRawMemManager : public OpSemMemManagerBase {
private:
  RawMemManager m_main;
  RawMemManager m_metadata;

  static const unsigned int g_MetadataBitWidth = 8;
  static const unsigned int g_MetadataByteWidth = g_MetadataBitWidth / 8;
  static const unsigned int g_num_slots = 2;

public:
  using PtrTy = OpSemMemManager::PtrTy;
  using PtrSortTy = OpSemMemManager::PtrSortTy;
  using MemRegTy = OpSemMemManager::MemRegTy;
  using RawMemValTy = OpSemMemManager::MemValTy;
  using RawMemSortTy = OpSemMemManager::MemSortTy;

  struct MemValTyImpl {
    Expr m_v;

    MemValTyImpl(RawMemValTy &&raw_val, Expr &&metadata_val) {
      assert(!strct::isStructVal(raw_val));
      assert(!strct::isStructVal(metadata_val));
      m_v = strct::mk(std::move(raw_val), std::move(metadata_val));
    }

    MemValTyImpl(const RawMemValTy &raw_val, const RawMemValTy &metadata_val) {
      assert(!strct::isStructVal(raw_val));
      assert(!strct::isStructVal(metadata_val));
      m_v = strct::mk(raw_val, metadata_val);
    }

    explicit MemValTyImpl(const Expr &e) {
      // Our base is a struct of two exprs
      assert(strct::isStructVal(e));
      assert(!strct::isStructVal(e->arg(0)));
      assert(!strct::isStructVal(e->arg(1)));
      assert(e->arity() == g_num_slots);
      m_v = e;
    }

    Expr v() const { return m_v; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }

    RawMemValTy getRaw() { return strct::extractVal(m_v, 0); }

    Expr getMetadata() { return strct::extractVal(m_v, 1); }
  };

  struct MemSortTyImpl {
    Expr m_mem_sort;

    MemSortTyImpl(RawMemSortTy &&mem_sort, Expr &&metadata_sort) {
      m_mem_sort =
          sort::structTy(std::move(mem_sort), std::move(metadata_sort));
    }

    MemSortTyImpl(const RawMemSortTy &mem_sort, Expr &metadata_sort) {
      m_mem_sort = sort::structTy(mem_sort, metadata_sort);
    }
    Expr v() const { return m_mem_sort; }
    Expr toExpr() const { return v(); }
    explicit operator Expr() const { return toExpr(); }
  };

  using MemValTy = MemValTyImpl;
  using MemSortTy = MemSortTyImpl;

  TrackingRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                        unsigned wordSz, bool useLambdas);

  TrackingRawMemManager(Bv2OpSem &sem, Bv2OpSemContext &ctx, unsigned ptrSz,
                        unsigned wordSz, bool useLambdas, bool ignoreAlignment);

  ~TrackingRawMemManager() = default;

  OpSemAllocator &getMAllocator() const { return m_main.getMAllocator(); }

  const OpSemMemManager &getMainMemMgr() const { return m_main; }

  PtrSortTy ptrSort() const { return m_main.ptrSort(); }

  PtrTy salloc(unsigned int bytes, uint32_t align) {
    return m_main.salloc(bytes, align);
  }

  PtrTy salloc(Expr elmts, unsigned int typeSz, uint32_t align) {
    return m_main.salloc(elmts, typeSz, align);
  }

  PtrTy mkStackPtr(unsigned int offset) { return m_main.mkStackPtr(offset); }

  PtrTy brk0Ptr() { return m_main.brk0Ptr(); }

  PtrTy halloc(unsigned int _bytes, uint32_t align) {
    return m_main.halloc(_bytes, align);
  }

  PtrTy halloc(Expr bytes, uint32_t align) {
    return m_main.halloc(bytes, align);
  }

  PtrTy galloc(const GlobalVariable &gv, uint32_t align) {
    return m_main.galloc(gv, align);
  }

  PtrTy falloc(const Function &fn) { return m_main.falloc(fn); }
  PtrTy getPtrToFunction(const Function &F) {
    return m_main.getPtrToFunction(F);
  }

  PtrTy getPtrToGlobalVariable(const GlobalVariable &gv) {
    return m_main.getPtrToGlobalVariable(gv);
  }

  void initGlobalVariable(const GlobalVariable &gv) const {
    return m_main.initGlobalVariable(gv);
  }

  PtrTy mkAlignedPtr(Expr name, uint32_t align) const {
    return m_main.mkAlignedPtr(name, align);
  }

  PtrSortTy mkPtrRegisterSort(const Instruction &inst) const {
    return m_main.mkPtrRegisterSort(inst);
  }

  PtrSortTy mkPtrRegisterSort(const Function &fn) const {
    return m_main.mkPtrRegisterSort(fn);
  }

  PtrSortTy mkPtrRegisterSort(const GlobalVariable &gv) const {
    return m_main.mkPtrRegisterSort(gv);
  }

  MemSortTy mkMemRegisterSort(const Instruction &inst) const {
    return MemSortTy(m_main.mkMemRegisterSort(inst),
                     m_metadata.mkMemRegisterSort(inst));
  }

  PtrTy freshPtr() { return m_main.freshPtr(); }

  PtrTy nullPtr() const { return m_main.nullPtr(); }

  // We expect to get ONLY the following sorts:
  // 1. MemSortTy which is a struct with two members
  // 2. PtrSortTy  or Expr which is not a struct
  Expr coerce(Expr sort, Expr val) {
    if (strct::isStructVal(val)) {
      llvm::SmallVector<Expr, g_num_slots> kids;
      assert(isOp<STRUCT_TY>(sort));
      assert(sort->arity() == val->arity());
      assert(sort->arity() == g_num_slots);
      kids.push_back(m_main.coerce(sort->arg(0), val->arg(0)));
      kids.push_back(m_metadata.coerce(sort->arg(1), val->arg(1)));
      return strct::mk(kids);
    }
    return m_main.coerce(sort, val);
  }

  PtrTy ptrAdd(PtrTy ptr, int32_t _offset) const {
    return m_main.ptrAdd(ptr, _offset);
  }

  PtrTy ptrAdd(PtrTy ptr, Expr offset) const {
    return m_main.ptrAdd(ptr, offset);
  }

  RawMemValTy memsetMetaData(const PtrTy ptr, unsigned int len, MemValTy memIn,
                             uint32_t align, unsigned int val) {
    // make sure we can fit the supplied value in metadata memory slot
    assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth);
    return m_metadata.MemSet(ptr, m_ctx.alu().si(val, g_MetadataBitWidth), len,
                             memIn.getMetadata(), align);
  }

  RawMemValTy memsetMetaData(const PtrTy ptr, Expr len, MemValTy memIn,
                             uint32_t align, unsigned int val) {
    // make sure we can fit the supplied value in metadata memory slot
    assert(llvm::Log2_64(val) + 1 <= g_MetadataBitWidth);
    return m_metadata.MemSet(ptr, m_ctx.alu().si(val, g_MetadataBitWidth), len,
                             memIn.getMetadata(), align);
  }

  // This function reports a warning if there is a possibily for the
  // passed value to not be equal to 1.
  // This implies we tried to load memory that was never stored into.
  void CheckDefBeforeUse(Expr val) {
    // assert(toCheck == 1)
    Expr toCheck = mk<NEQ>(val, m_ctx.alu().si(1, g_MetadataBitWidth));
    // We need to reset the solver everytime since two checks will
    // need to remove expressions from the solver.
    m_ctx.resetSolver();

    for (auto e : m_ctx.side()) {
      m_ctx.addToSolver(e);
    }
    m_ctx.addToSolver(m_ctx.getPathCond());
    m_ctx.addToSolver(toCheck);
    auto result = m_ctx.solve();
    if (result) {
      const Instruction &I = m_ctx.getCurrentInst();
      auto dloc = I.getDebugLoc();
      if (dloc) {
        WARN << "Found Use before Def!"
             << "[" << dloc->getFilename() << ":" << dloc->getLine() << "]";
      } else {
        WARN << "Found Use before Def!"
             << "[" << I << "]";
      }
    }
  }

  Expr loadIntFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                      uint64_t align) {
    Expr res = m_main.loadIntFromMem(ptr, mem.getRaw(), byteSz, align);
    Expr metadata = m_metadata.loadIntFromMem(ptr, mem.getMetadata(),
                                              g_MetadataByteWidth, align);
    CheckDefBeforeUse(metadata);
    return res;
  }

  PtrTy loadPtrFromMem(PtrTy ptr, MemValTy mem, unsigned int byteSz,
                       uint64_t align) {
    PtrTy rawPtr = m_main.loadPtrFromMem(ptr, mem.getRaw(), byteSz, align);
    Expr metadata =
        m_metadata.loadIntFromMem(ptr, mem.getMetadata(), byteSz, align);
    CheckDefBeforeUse(metadata);
    return rawPtr;
  }

  MemValTy storeIntToMem(Expr _val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align) {
    // We expect _val to be a primitive rather than a container
    assert(!strct::isStructVal(_val));
    RawMemValTy rawVal =
        m_main.storeIntToMem(_val, ptr, mem.getRaw(), byteSz, align);
    // Number of slots to fill with '1' depends on slot size i.e
    // g_MetadataByteWidth
    unsigned int len = byteSz / g_MetadataByteWidth;
    RawMemValTy metadataVal = memsetMetaData(ptr, len, mem, align, 1U);
    return MemValTy(rawVal, metadataVal);
  }

  MemValTy storePtrToMem(PtrTy val, PtrTy ptr, MemValTy mem,
                         unsigned int byteSz, uint64_t align) {
    RawMemValTy rawVal =
        m_main.storePtrToMem(val, ptr, mem.getRaw(), byteSz, align);
    // Number of slots to fill with '1' depends on slot size i.e
    // g_MetadataByteWidth
    unsigned int len = byteSz / g_MetadataByteWidth;
    RawMemValTy metadataVal = memsetMetaData(ptr, len, mem, align, 1U);
    return MemValTy(rawVal, metadataVal);
  }

  Expr loadValueFromMem(PtrTy ptr, MemValTy mem, const Type &ty,
                        uint64_t align) {
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
    }
    return res;
  }

  MemValTy storeValueToMem(Expr _val, PtrTy ptr, MemValTy memIn, const Type &ty,
                           uint32_t align) {
    assert(ptr);
    Expr val = _val;
    const unsigned byteSz =
        m_sem.getTD().getTypeStoreSize(const_cast<llvm::Type *>(&ty));
    ExprFactory &efac = ptr->efac();
    // TODO: use zeroed memory on m_main, m_metadata instead of explicit
    // init
    MemValTy res(m_ctx.alu().si(0UL, wordSzInBits()),
                 m_ctx.alu().si(0UL, g_MetadataBitWidth));
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
    }
    return res;
  }

  MemValTy MemSet(PtrTy ptr, Expr _val, unsigned int len, MemValTy mem,
                  uint32_t align) {
    RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
    return MemValTy(rawVal, memsetMetaData(ptr, len, mem, align, 1U));
  }

  MemValTy MemSet(PtrTy ptr, Expr _val, Expr len, MemValTy mem,
                  uint32_t align) {
    RawMemValTy rawVal = m_main.MemSet(ptr, _val, len, mem.getRaw(), align);
    return MemValTy(rawVal, memsetMetaData(ptr, len, mem, align, 1U));
  }

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, unsigned int len,
                  MemValTy memTrsfrRead, MemValTy memRead, uint32_t align) {
    RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                       memRead.getRaw(), align);
    return MemValTy(rawVal, memsetMetaData(dPtr, len, memTrsfrRead, align, 1U));
  }

  MemValTy MemCpy(PtrTy dPtr, PtrTy sPtr, Expr len, MemValTy memTrsfrRead,
                  MemValTy memRead, uint32_t align) {
    RawMemValTy rawVal = m_main.MemCpy(dPtr, sPtr, len, memTrsfrRead.getRaw(),
                                       memRead.getRaw(), align);
    return MemValTy(rawVal, memsetMetaData(dPtr, len, memTrsfrRead, align, 1U));
  }

  MemValTy MemFill(PtrTy dPtr, char *sPtr, unsigned int len, MemValTy mem,
                   uint32_t align) {
    RawMemValTy rawVal = m_main.MemFill(dPtr, sPtr, len, mem.getRaw(), align);
    return MemValTy(rawVal, memsetMetaData(dPtr, len, mem, align, 1U));
  }

  PtrTy inttoptr(Expr intVal, const Type &intTy, const Type &ptrTy) const {
    return m_main.inttoptr(intVal, intTy, ptrTy);
  }

  Expr ptrtoint(PtrTy ptr, const Type &ptrTy, const Type &intTy) const {
    return m_main.ptrtoint(ptr, ptrTy, intTy);
  }

  Expr ptrEq(PtrTy p1, PtrTy p2) const { return m_main.ptrEq(p1, p2); }

  PtrTy gep(PtrTy ptr, gep_type_iterator it, gep_type_iterator end) const {
    return m_main.gep(ptr, it, end);
  }
  void onFunctionEntry(const Function &fn) { m_main.onFunctionEntry(fn); }
  void onModuleEntry(const Module &M) { m_main.onModuleEntry(M); }

  void dumpGlobalsMap() { m_main.dumpGlobalsMap(); }

  std::pair<char *, unsigned int>
  getGlobalVariableInitValue(const GlobalVariable &gv) {
    return m_main.getGlobalVariableInitValue(gv);
  }

  MemValTy zeroedMemory() const {
    return MemValTy(m_main.zeroedMemory(), m_metadata.zeroedMemory());
  }

  Expr isDereferenceable(PtrTy p, Expr byteSz) {
    // isDereferenceable should never be called in a 'RawMemMgr'
    return m_ctx.alu().getFalse();
  }

  PtrTy getAddressable(PtrTy p) const { return p; }
};

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas)
    : OpSemMemManagerBase(
          sem, ctx, ptrSz, wordSz,
          false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas),
      m_metadata(sem, ctx, ptrSz, g_MetadataByteWidth, useLambdas, true) {}

TrackingRawMemManager::TrackingRawMemManager(Bv2OpSem &sem,
                                             Bv2OpSemContext &ctx,
                                             unsigned ptrSz, unsigned wordSz,
                                             bool useLambdas,
                                             bool ignoreAlignment)
    : OpSemMemManagerBase(
          sem, ctx, ptrSz, wordSz,
          false /* this is a nop since we delegate to RawMemMgr */),
      m_main(sem, ctx, ptrSz, wordSz, useLambdas, ignoreAlignment),
      m_metadata(sem, ctx, ptrSz, g_MetadataByteWidth, useLambdas, true) {}

} // namespace details
} // namespace seahorn
