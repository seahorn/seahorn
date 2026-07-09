#ifndef _CAN_ACCESS_MEMORY__HH_
#define _CAN_ACCESS_MEMORY__HH_

/**
 * Identifies which functions may access to memory
 */

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseSet.h"

namespace seahorn
{
  using namespace llvm;
  
  class CanAccessMemory : public ModulePass
  {
    /// functions that must access memory
    DenseSet<const Function*> m_must;
    /// functions that may access memory
    DenseSet<const Function*> m_may;
    
  public:
    static char ID;
    
    CanAccessMemory () : ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M) override;
    virtual void getAnalysisUsage (AnalysisUsage &AU) const override ;
    bool canAccess (const Function *f) const;
    bool mustAccess (const Function *f) const
    {return m_must.count (f) > 0;}
    virtual StringRef getPassName () const override {return "CanAccessMemory";}
    
  };
}
#endif 
