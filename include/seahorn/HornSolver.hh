#ifndef HORN_SOLVER__HH_
#define HORN_SOLVER__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

#include "boost/logic/tribool.hpp"
namespace seahorn
{
  using namespace llvm;

  class HornSolver : public llvm::ModulePass
  {
    boost::tribool m_result;
    
    void printInvars (Function &F);
    void printInvars (Module &M);
    void printCex ();
    
  public:
    static char ID;
    
    HornSolver () : ModulePass(ID), m_result(boost::indeterminate) {}
    virtual ~HornSolver() {}
    
    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "HornSolver";}
    
    boost::tribool getResult () {return m_result;}
    
  };

}

#endif /* HORN_SOLVER__HH_ */
