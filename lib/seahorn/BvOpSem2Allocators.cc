#include "BvOpSem2Context.hh"

#include "llvm/IR/GetElementPtrTypeIterator.h"
#include "llvm/Support/Format.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "ufo/ExprLlvm.hpp"

namespace seahorn {
namespace details {

using AddrInterval = OpSemAllocator::AddrInterval;

OpSemAllocator::OpSemAllocator(OpSemMemManager &mgr)
    : m_mgr(mgr), m_ctx(mgr.ctx()), m_sem(mgr.sem()),
      m_efac(m_ctx.getExprFactory()) {}

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

} // namespace details
} // namespace seahorn
