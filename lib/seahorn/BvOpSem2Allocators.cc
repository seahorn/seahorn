#include "BvOpSem2Context.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/Format.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "ufo/ExprLlvm.hpp"

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

  AllocInfo(unsigned id, unsigned start, unsigned end, unsigned sz)
      : m_id(id), m_start(start), m_end(end), m_sz(sz) {}
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

    m_mem = static_cast<char *>(::operator new(sz));
  }

  char *getMemory() { return m_mem; }
};

OpSemAllocator::OpSemAllocator(OpSemMemManager &mgr)
    : m_mgr(mgr), m_ctx(mgr.ctx()), m_sem(mgr.sem()),
      m_efac(m_ctx.getExprFactory()) {}

OpSemAllocator::~OpSemAllocator() = default;

/// \brief Allocates memory on the stack and returns a pointer to it
/// \param align is requested alignment. If 0, default alignment is used
AddrInterval OpSemAllocator::salloc(unsigned bytes, uint32_t align) {
  unsigned start = m_allocas.empty() ? 0 : m_allocas.back().m_end;
  start = llvm::alignTo(start, align);

  unsigned end = start + bytes;
  end = llvm::alignTo(end, align);

  m_allocas.emplace_back(m_allocas.size() + 1, start, end, bytes);

  return std::make_pair(m_allocas.back().m_start, m_allocas.back().m_end);
}

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
  m_sem.initMemory(gv.getInitializer(), m_globals.back().getMemory());
  return std::make_pair(start, end);
}

AddrInterval OpSemAllocator::falloc(const Function &fn, unsigned alignment) {
  assert(m_globals.empty() && "Cannot allocate functions after globals");
  unsigned start = m_funcs.empty() ? 0x08048000 : m_funcs.back().m_end;
  unsigned end = llvm::alignTo(start + 4, alignment);
  m_funcs.emplace_back(fn, start, end);
  return std::make_pair(start, end);
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

std::unique_ptr<OpSemAllocator> mkOpSemAllocator(OpSemMemManager &mgr) {
  return llvm::make_unique<OpSemAllocator>(mgr);
}

} // namespace details
} // namespace seahorn
