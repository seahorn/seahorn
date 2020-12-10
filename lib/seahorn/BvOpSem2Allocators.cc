#include "BvOpSem2Allocators.hh"
#include "BvOpSem2Context.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/Format.h"

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

namespace seahorn {
namespace details {

using AddrInterval = OpSemAllocator::AddrInterval;

/// \brief Allocation information
struct OpSemAllocator::AllocInfo {
  /// \brief numeric ID
  unsigned m_id;
  /// \brief Start address of the allocation
  unsigned m_start;
  /// \brief End address of the allocation
  unsigned m_end;
  /// \brief Size of the allocation
  unsigned m_sz;
  /// \brief Instruction that caused the allocation
  const AllocaInst *m_inst;
  /// \brief True if this is a fixed size allocation
  bool m_fixed;

  AllocInfo(unsigned id, unsigned start, unsigned end, unsigned sz,
            const AllocaInst *inst = nullptr, bool fixed = true)
      : m_id(id), m_start(start), m_end(end), m_sz(sz), m_inst(inst),
        m_fixed(fixed) {}
};

/// \brief Allocation information for functions whose address is taken
struct OpSemAllocator::FuncAllocInfo {
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
struct OpSemAllocator::GlobalAllocInfo {
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

    m_mem = static_cast<char *>(::operator new(end - start));
  }

  char *getMemory() const { return m_mem; }
};

OpSemAllocator::OpSemAllocator(RawMemManagerCore &mem, unsigned maxSymbAllocSz)
    : m_mem(mem), m_ctx(mem.ctx()), m_sem(mem.sem()),
      m_efac(m_ctx.getExprFactory()), m_maxSymbAllocSz(maxSymbAllocSz) {}

OpSemAllocator::~OpSemAllocator() = default;

/// \brief Address at which heap starts (initial value of \c brk)
unsigned OpSemAllocator::brk0Addr() {
  if (!m_globals.empty())
    return m_globals.back().m_end;
  if (!m_funcs.empty())
    return m_funcs.back().m_end;
  return TEXT_SEGMENT_START;
}

/// \brief Allocates memory in global (data/bss) segment for given global
AddrInterval OpSemAllocator::galloc(const GlobalVariable &gv, uint64_t bytes,
                                    unsigned align) {
  unsigned start =
      !m_globals.empty()
          ? m_globals.back().m_end
          : (m_funcs.empty() ? TEXT_SEGMENT_START : m_funcs.back().m_end);

  start = llvm::alignTo(start, align);
  unsigned end = llvm::alignTo(start + bytes, align);
  m_globals.emplace_back(gv, start, end, bytes);
  return std::make_pair(start, end);
}

AddrInterval OpSemAllocator::falloc(const Function &fn, unsigned alignment) {
  assert(m_globals.empty() && "Cannot allocate functions after globals");
  unsigned start = m_funcs.empty() ? TEXT_SEGMENT_START : m_funcs.back().m_end;
  unsigned end = llvm::alignTo(start + 4, alignment);
  m_funcs.emplace_back(fn, start, end);
  return std::make_pair(start, end);
}

/// \brief Returns an address at which a given function resides
AddrInterval OpSemAllocator::getFunctionAddrAndSize(const Function &F,
                                                    unsigned align) {
  for (auto &fi : m_funcs)
    if (fi.m_fn == &F)
      return {fi.m_start, fi.m_end};
  falloc(F, align);
  return {m_funcs.back().m_start, m_funcs.back().m_end};
}

/// \brief Returns an address at which a given function resides
unsigned OpSemAllocator::getFunctionAddr(const Function &F, unsigned align) {
  for (auto &fi : m_funcs)
    if (fi.m_fn == &F)
      return fi.m_start;
  falloc(F, align);
  return m_funcs.back().m_start;
}

/// \brief Returns an address of a global variable
unsigned OpSemAllocator::getGlobalVariableAddr(const GlobalVariable &gv,
                                               unsigned bytes, unsigned align) {
  for (auto &gi : m_globals)
    if (gi.m_gv == &gv)
      return gi.m_start;

  galloc(gv, bytes, align);
  return m_globals.back().m_start;
}

/// \brief Returns an address of memory segment to store value of the variable
char *OpSemAllocator::getGlobalVariableMem(const GlobalVariable &gv) const {
  for (auto &gi : m_globals)
    if (gi.m_gv == &gv)
      return gi.getMemory();

  return nullptr;
}

/// \brief Returns initial value of a global variable
///
/// Returns (nullptr, 0) if the global variable has no known initializer
std::pair<char *, unsigned>
OpSemAllocator::getGlobalVariableInitValue(const GlobalVariable &gv) {
  for (auto &gi : m_globals) {
    if (gi.m_gv == &gv)
      return std::make_pair(gi.m_mem, gi.m_sz);
  }
  return std::make_pair(nullptr, 0);
}

/// \brief Debug helper
void OpSemAllocator::dumpGlobalsMap() {
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

class NormalOpSemAllocator : public OpSemAllocator {
public:
  NormalOpSemAllocator(RawMemManagerCore &mem, unsigned maxSymbAllocSz)
      : OpSemAllocator(mem, maxSymbAllocSz) {}
  ~NormalOpSemAllocator() = default;

  /// \brief Allocates memory on the stack and returns a pointer to it
  /// \param align is requested alignment. If 0, default alignment is used
  AddrInterval salloc(unsigned bytes, uint32_t align) override {
    unsigned start = m_allocas.empty() ? 0 : m_allocas.back().m_end;
    start = llvm::alignTo(start, align);

    unsigned end = start + bytes;
    end = llvm::alignTo(end, align);

    const AllocaInst *alloca = dyn_cast<AllocaInst>(&m_ctx.getCurrentInst());
    m_allocas.emplace_back(m_allocas.size() + 1, start, end, bytes, alloca,
                           true);

    return std::make_pair(m_allocas.back().m_start, m_allocas.back().m_end);
  }

  AddrInterval salloc(Expr bytes, uint32_t align) override {
    auto addrIvl = this->salloc(m_maxSymbAllocSz, align);
    auto width = m_mem.ptrSizeInBits();
    Expr inRange = m_ctx.alu().doUle(
        bytes, m_ctx.alu().ui(m_maxSymbAllocSz, width), width);
    m_ctx.addScopedRely(inRange);
    return addrIvl;
  }
};

/// \brief Allocator that statically pre-allocates memory regions
///
/// A fixed number (typically 1) memory region is allocated for each
/// allocation instruction in the program under analysis.
/// Dynamically sized allocations are under-approximated.
///
/// This allocator under-approximates concrete behavior that might cause
/// unsoundness depending on the use / expectations. Use with caution
class StaticOpSemAllocator : public OpSemAllocator {
public:
  StaticOpSemAllocator(RawMemManagerCore &mem, unsigned maxSymbAllocSz)
      : OpSemAllocator(mem, maxSymbAllocSz) {}

  void onModuleEntry(const Module &M) override {
    // TODO: pre-allocate all globals of M

    for (const Function &fn : M.functions()) {
      if (fn.hasAddressTaken()) {
        // XXX hard-coded. should be based on use
        // XXX some functions have their address taken for llvm.used
        if (fn.getName().equals("verifier.error") ||
            fn.getName().startswith("verifier.assume") ||
            fn.getName().equals("seahorn.fail") ||
            fn.getName().startswith("shadow.mem"))
          continue;
        OpSemAllocator::falloc(fn, m_mem.getAlignment(fn));
      }
    }

    for (const GlobalVariable &gv : M.globals()) {
      if (m_sem.isSkipped(gv))
        continue;
      if (gv.getSection().equals("llvm.metadata")) {
        continue;
      }
      uint64_t bytes = m_sem.getTD().getTypeAllocSize(gv.getValueType());
      OpSemAllocator::galloc(gv, bytes, m_mem.getAlignment(gv));
    }
  }

  AddrInterval galloc(const GlobalVariable &gv, uint64_t bytes,
                      unsigned align) override {
    for (auto &gi : m_globals)
      if (gi.m_gv == &gv)
        return {gi.m_start, gi.m_end};
    return {0, 0};
  }

  AddrInterval falloc(const Function &fn, unsigned align) override {
    for (auto &fi : m_funcs)
      if (fi.m_fn == &fn)
        return {fi.m_start, fi.m_end};
    return {0, 0};
  }

  void onFunctionEntry(const Function &fn) override {

    for (auto &inst : instructions(fn)) {
      if (auto *alloca = dyn_cast<AllocaInst>(&inst)) {
        preAlloc(*alloca);
      }
    }
  }

  /// \brief Pre-allocate memory for alloca
  void preAlloc(const AllocaInst &inst) {
    Type *ty = inst.getType()->getElementType();
    unsigned typeSz = (size_t)m_sem.getTD().getTypeAllocSize(ty);

    if (const Constant *cv = dyn_cast<const Constant>(inst.getOperand(0))) {
      ConstantExprEvaluator ce(m_sem.getDataLayout());
      auto ogv = ce.evaluate(cv);
      if (!ogv.hasValue()) {
        llvm_unreachable(nullptr);
      }
      unsigned nElts = ogv.getValue().IntVal.getZExtValue();
      unsigned memSz = typeSz * nElts;
      preAlloc(inst, memSz, true);
    } else {
      // -- allocate max allowed for dynamically sized allocations
      preAlloc(inst, m_maxSymbAllocSz, false);
    }
  }

  void preAlloc(const AllocaInst &inst, unsigned bytes,
                bool isFixedSize = false) {
    unsigned start = m_allocas.empty() ? 0 : m_allocas.back().m_end;
    uint32_t align = m_mem.getAlignment(inst);
    start = llvm::alignTo(start, align);

    unsigned end = start + bytes;
    end = llvm::alignTo(end, align);

    m_allocas.emplace_back(m_allocas.size() + 1, start, end, bytes, &inst,
                           isFixedSize);
  }

  AddrInterval salloc(unsigned bytes, uint32_t align) override {
    if (auto *alloca = dyn_cast<llvm::AllocaInst>(&m_ctx.getCurrentInst())) {
      for (auto &ai : m_allocas) {
        if (ai.m_inst == alloca)
          return {ai.m_start, ai.m_end};
      }
    }
    return {0, 0};
  }

  AddrInterval salloc(Expr bytes, uint32_t align = 0) override {
    if (auto *alloca = dyn_cast<llvm::AllocaInst>(&m_ctx.getCurrentInst())) {
      for (auto &ai : m_allocas) {
        if (ai.m_inst == alloca) {
          auto width = m_mem.ptrSizeInBits();
          Expr inRange = m_ctx.alu().doUle(
              bytes, m_ctx.alu().ui(m_maxSymbAllocSz, width), width);
          LOG("opsem", errs()
                           << "Adding range condition: " << *inRange << "\n";);
          m_ctx.addScopedRely(inRange);
          return {ai.m_start, ai.m_end};
        }
      }
    }
    return {0, 0};
  }
};
std::unique_ptr<OpSemAllocator>
mkNormalOpSemAllocator(RawMemManagerCore &mem, unsigned maxSymbAllocSz) {
  return std::make_unique<NormalOpSemAllocator>(mem, maxSymbAllocSz);
}
std::unique_ptr<OpSemAllocator>
mkStaticOpSemAllocator(RawMemManagerCore &mem, unsigned maxSymbAllocSz) {
  return std::make_unique<StaticOpSemAllocator>(mem, maxSymbAllocSz);
}

} // namespace details
} // namespace seahorn
