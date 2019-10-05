#ifndef HORN_SOLVER__HH_
#define HORN_SOLVER__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "boost/logic/tribool.hpp"
#include "seahorn/HornDbModel.hh"

#include "seahorn/Expr/Smt/EZ3.hh"

namespace seahorn
{
  using namespace llvm;

  class HornSolver : public llvm::ModulePass
  {
    boost::tribool m_result;
    std::unique_ptr<ZFixedPoint <EZ3> >  m_fp;
    
    void printCex ();
    void estimateSizeInvars (Module &M);

    void printInvars(Function &F, HornDbModel &model);
    void printInvars(Module &M, HornDbModel &model);

  public:
    static char ID;
    
    HornSolver () : ModulePass(ID), m_result(boost::indeterminate) {}
    virtual ~HornSolver() {}
    
    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual StringRef getPassName () const {return "HornSolver";}
    ZFixedPoint<EZ3>& getZFixedPoint () {return *m_fp;}
    
    boost::tribool getResult () {return m_result;}
    void releaseMemory () {m_fp.reset (nullptr);}
    
  };

}

#endif /* HORN_SOLVER__HH_ */
