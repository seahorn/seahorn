#ifndef __MEM_SIMULATOR__HH_
#define __MEM_SIMULATOR__HH_
#include "seahorn/Bmc.hh"

#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/TargetLibraryInfo.h"

namespace seahorn
{
  using namespace expr;
  using namespace llvm;
  
  /// Simulate memory based on a BmcTrace
  class MemSimulator
  {

    struct AllocInfo
    {
      unsigned id;
      unsigned start;
      unsigned end;
    };
    
    std::vector<AllocInfo> m_allocs;
    
    const DataLayout &m_dl;
    const TargetLibraryInfo &m_tli;
    
    // -- start byte of external memory
    unsigned m_extMemStart;
    // -- end byte of external memory
    unsigned m_extMemEnd;

    // -- start of internally allocated memory
    unsigned m_intMemStart;

    BmcTrace &m_trace;
    ufo::ZModel<ufo::EZ3> m_model;

    ufo::EZ3 &zctx () { return m_trace.engine ().zctx (); }
  public:
    MemSimulator (BmcTrace &bmc_trace,
                  const DataLayout &dl, const TargetLibraryInfo &tli) :
      m_dl (dl), m_tli (tli),
      m_intMemStart (10 * 1024 * 1024),
      m_trace (bmc_trace), m_model (zctx()) {}
    
    const AllocInfo &alloc (unsigned sz);
    
    BmcTrace &trace () {return m_trace;}
    
    // -- run simulation
    bool simulate ();

    Expr eval (unsigned loc, const llvm::Instruction &inst, bool complete=false);
    
    const DataLayout &getDataLayout () {return m_dl;}
    const TargetLibraryInfo &getTargetLibraryInfo () {return m_tli;}
  };
}

#endif
