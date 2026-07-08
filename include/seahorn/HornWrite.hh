#ifndef _HORN_WRITE__HH__
#define _HORN_WRITE__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

namespace seahorn
{
  class HornifyModule;
  using namespace llvm;
  
  
  class HornWrite : public llvm::ModulePass
  {
    llvm::raw_fd_ostream& m_out;
  public:
    static char ID;
    HornWrite (llvm::raw_fd_ostream &out) : llvm::ModulePass (ID), m_out (out) {}
    virtual ~HornWrite() = default;
    virtual StringRef getPassName() const override {return "HornWrite";}
    
    virtual bool runOnModule(Module &M) override;
    bool runImpl(Module &M, HornifyModule &hm);
    virtual void getAnalysisUsage(AnalysisUsage &AU) const override;
  };
}



#endif /* _HORN_WRITE__HH__ */
