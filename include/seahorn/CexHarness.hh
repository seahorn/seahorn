#ifndef _CEXHARNESS__HH_
#define _CEXHARNESS__HH_

#include "llvm/ADT/StringRef.h"

#include "seahorn/Bmc.hh"
#include "seahorn/MemSimulator.hh"

namespace llvm {
class TargetLibraryInfo;
class DataLayout;
class LLVMContext;
class Module;
}

namespace seahorn {

class BmcTraceWrapper;

/**
 * createCexHarness: given a BMC trace (cex) it produces a harness
 * written in LLVM bitcode.  A harness is a LLVM module containing the
 * implementation of all external calls visited by the
 * counterexample.
 **/
std::unique_ptr<llvm::Module> createCexHarness(BmcTraceWrapper &trace,
                                               const llvm::DataLayout &dl,
                                               const llvm::TargetLibraryInfo &tli,
                                               llvm::LLVMContext &context);

void dumpLLVMCex(BmcTraceWrapper &trace, llvm::StringRef CexFile,
		 const llvm::DataLayout &dl, const llvm::TargetLibraryInfo &tli,
		 llvm::LLVMContext &context);

} // end namespace seahorn


namespace seahorn {

// Wrapper for BmcTrace and MemSimulator objects.
//
// Both are defined wrt to the same BmcTrace but they can have
// different models associated (accessed via the virtual method
// eval).
class BmcTraceWrapper {
  BmcTrace &m_trace;

public:
  BmcTraceWrapper(BmcTrace &trace) : m_trace(trace) {}

  /// access to expression factory
  ExprFactory &efac() { return m_trace.engine().efac(); }

  /// The number of basic blocks in the trace
  virtual unsigned size() const { return m_trace.size(); }

  /// The basic block at a given location
  virtual const llvm::BasicBlock *bb(unsigned loc) const {
    return m_trace.bb(loc);
  }

  /// The value of the instruction at the given location
  virtual Expr eval(unsigned loc, const llvm::Instruction &inst, bool complete);
  virtual Expr eval(unsigned loc, Expr v, bool complete);
};

class BmcTraceMemSim : public BmcTraceWrapper {
  MemSimulator &m_mem_sim;

public:
  BmcTraceMemSim(MemSimulator &mem_sim)
      : BmcTraceWrapper(mem_sim.trace()), m_mem_sim(mem_sim) {}

  virtual Expr eval(unsigned loc, const llvm::Instruction &inst,
                    bool complete) override;
  virtual Expr eval(unsigned loc, Expr v, bool complete) override;
};

} // namespace seahorn

#endif
