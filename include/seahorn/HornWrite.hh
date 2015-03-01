#ifndef _HORN_WRITE__HH__
#define _HORN_WRITE__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

namespace seahorn
{
  using namespace llvm;
  
  
  class HornWrite : public llvm::ModulePass
  {
    llvm::raw_fd_ostream& m_out;
  public:
    static char ID;
    HornWrite (llvm::raw_fd_ostream &out) : llvm::ModulePass (ID), m_out (out) {}
    virtual ~HornWrite () {} 
    virtual const char* getPassName () const {return "HornWrite";}
    
    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
  };
}



#endif /* _HORN_WRITE__HH__ */
