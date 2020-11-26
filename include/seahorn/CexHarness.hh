#ifndef _CEXHARNESS__HH_
#define _CEXHARNESS__HH_

#include "llvm/ADT/StringRef.h"

#include "seahorn/Bmc.hh"
#include "seahorn/MemSimulator.hh"
#include "seahorn/SolverBmc.hh"

namespace llvm {
class TargetLibraryInfo;
class DataLayout;
class LLVMContext;
class Module;
}

namespace seahorn {

template <class Trace> class BmcTraceWrapper;

Constant *exprToLlvm(Type *ty, Expr e, LLVMContext &ctx, const DataLayout &dl);

/* Given Expr of a shadow.mem segment and pre-recorded size Value
   use HexDump to extract const array with item size of current
   word size from Expr
*/
Constant *exprToMemSegment(Expr segment, Expr startAddr, Expr size,
                           llvm::LLVMContext &ctx, const llvm::DataLayout &dl);

/**
 * createCexHarness: given a BMC trace (cex) it produces a harness
 * written in LLVM bitcode.  A harness is a LLVM module containing the
 * implementation of all external calls visited by the
 * counterexample.
 **/
template <class Trace>
std::unique_ptr<llvm::Module>
createCexHarness(BmcTraceWrapper<Trace> &trace, const llvm::DataLayout &dl,
                 const llvm::TargetLibraryInfo &tli,
                 llvm::LLVMContext &context);

template <class Trace>
void dumpLLVMCex(BmcTraceWrapper<Trace> &trace, llvm::StringRef CexFile,
                 const llvm::DataLayout &dl, const llvm::TargetLibraryInfo &tli,
                 llvm::LLVMContext &context);

} // end namespace seahorn

template <typename IndexToValueMap>
bool extractArrayContents(Expr e, IndexToValueMap &out, Expr &default_value);

namespace seahorn {

// Wrapper for BmcTrace and MemSimulator objects.
//
// Both are defined wrt to the same BmcTrace but they can have
// different models associated (accessed via the virtual method
// eval).
template <class Trace> class BmcTraceWrapper {
  Trace &m_trace;

public:
  BmcTraceWrapper(Trace &trace) : m_trace(trace) {}

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

class BmcTraceMemSim : public BmcTraceWrapper<ZBmcTraceTy> {
  MemSimulator &m_mem_sim;

public:
  BmcTraceMemSim(MemSimulator &mem_sim)
      : BmcTraceWrapper(mem_sim.trace()), m_mem_sim(mem_sim) {}

  virtual Expr eval(unsigned loc, const llvm::Instruction &inst,
                    bool complete) override;
  virtual Expr eval(unsigned loc, Expr v, bool complete) override;
};

} // namespace seahorn

#include "seahorn/CexHarnessImpl.hh"

#endif
