#ifndef __SEAHORN_MAIN_HPP_
#define __SEAHORN_MAIN_HPP_

#include "llvm/Pass.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Support/raw_ostream.h"

namespace seahorn
{
  class SeahornMain : public llvm::ModulePass
  {

  public:
    static char ID;
    
    llvm::raw_fd_ostream& m_out;
    
    SeahornMain (llvm::raw_fd_ostream &out) : ModulePass (ID), m_out (out) {}
    
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual bool runOnModule (llvm::Module& M);
    // virtual bool runOnFunction (llvm::Function &F);
    bool runOnFunction (llvm::Function &F, bool IkosInvEnabled);
    virtual const char* getPassName () const {return "SeahornMain";}
    

  };
}


#endif
