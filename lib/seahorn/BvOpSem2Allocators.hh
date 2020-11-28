#pragma once

#include "BvOpSem2Context.hh"
#include "BvOpSem2RawMemMgr.hh"

namespace seahorn {
namespace details {

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

  RawMemManagerCore &m_mem;
  Bv2OpSemContext &m_ctx;
  Bv2OpSem &m_sem;
  ExprFactory &m_efac;

  /// \brief All known stack allocations
  std::vector<AllocInfo> m_allocas;
  /// \brief All known code allocations
  std::vector<FuncAllocInfo> m_funcs;
  /// \brief All known global allocations
  std::vector<GlobalAllocInfo> m_globals;

  /// \brief Maximal assumed size of symbolic allocation
  unsigned m_maxSymbAllocSz;

  // TODO: turn into user-controlled parameters
  const unsigned MAX_STACK_ADDR = 0xC0000000;
  const unsigned MIN_STACK_ADDR = (MAX_STACK_ADDR - 9437184);
  const unsigned TEXT_SEGMENT_START = 0x08048000;

public:
  using AddrInterval = std::pair<unsigned, unsigned>;
  explicit OpSemAllocator(RawMemManagerCore &mem,
                          unsigned maxSymbAllocSz = 4096);

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

  virtual AddrInterval getFunctionAddrAndSize(const Function &F,
                                              unsigned int align);

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
std::unique_ptr<OpSemAllocator>
mkNormalOpSemAllocator(RawMemManagerCore &mem, unsigned maxSymbAllocSz = 4096);
std::unique_ptr<OpSemAllocator>
mkStaticOpSemAllocator(RawMemManagerCore &mem, unsigned maxSymbAllocSz = 4096);

} // namespace details
} // namespace seahorn
