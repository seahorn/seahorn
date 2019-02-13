#ifndef _CAN_FAIL__HH_
#define _CAN_FAIL__HH_

/**
 * Identifies which functions may fail because of a call to verifier.error()
 */
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/ADT/DenseSet.h"

namespace seahorn
{
  using namespace llvm;
  
  class CanFail : public ModulePass
  {
    /// functions that must fail
    DenseSet<const Function*> m_must;
    /// functions that may fail
    DenseSet<const Function*> m_may;
    
  public:
    static char ID;
    
    CanFail () : ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    bool canFail (const Function *f) const;
    bool mustFail (const Function *f) const
    {return m_must.count (f) > 0;}

    StringRef getPassName () const override {return "Can Fail";}
  };
}
#endif /* _CAN_FAIL__HH_ */
