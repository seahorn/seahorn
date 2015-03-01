#include "seahorn/HornWrite.hh"
#include "seahorn/HornifyModule.hh"

#include "llvm/Support/CommandLine.h"

static llvm::cl::opt<bool>
InternalWriter("horn-fp-internal-writer",
               llvm::cl::desc("Use internal writer for Horn SMT2 format. (Default)"),
               llvm::cl::init(true),llvm::cl::Hidden);

namespace seahorn
{
  char HornWrite::ID = 0;
  
  void HornWrite::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll ();
  }
  
  bool HornWrite::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    if (InternalWriter)
      m_out << hm.getZFixedPoint () << "\n";
    else
      m_out << hm.getZFixedPoint ().toString () << "\n";
    m_out.flush ();
    
    return false;
  }
  
}
