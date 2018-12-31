#ifndef __BMC_FUNCTION__HH_
#define __BMC_FUNCTION__HH_

#include "seahorn/BMCModule.hh"
#include "llvm/IR/Function.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/UfoOpSem.hh"
#include "seahorn/LiveSymbols.hh"



namespace{

    inline const llvm::BasicBlock* findErrorBlock (const llvm::Function &F)
    {
      for (const llvm::BasicBlock& bb : F)
        if (llvm::isa<llvm::ReturnInst> (bb.getTerminator ())) return &bb;
      return NULL;
    }

}

namespace seabmc
{
  using namespace expr;
  using namespace llvm;
  

  class BMCFunction
  {
  protected:
    BMCModule &m_parent;

    SmallStepSymExec &m_sem;
    ZFixedPoint<EZ3> &m_fp;
    EZ3 &m_zctx;
    ExprFactory &m_efac;

    /// whether encoding is inter-procedural (i.e., with summaries)
    //bool m_interproc;

  public:
      BMCFunction (BMCModule &parent) :
          m_parent (parent), m_sem (m_parent.symExec ()),
          m_fp (m_parent.getZFixedPoint ()), m_zctx (m_fp.getContext ()),
          m_efac (m_zctx.getExprFactory ()) {}

      virtual ~BMCFunction () {}
      ZFixedPoint<EZ3> &getZFixedPoint () {return m_fp;}
      virtual void runOnFunction (Function &F) = 0;

  };

    class SmallBMCFunction : public BMCFunction
    {


    public:
        SmallBMCFunction (BMCModule &parent) :
            BMCFunction (parent) {}

        virtual void runOnFunction (Function &F);
    } ;

    class LargeBMCFunction : public BMCFunction
    {
    public:
        LargeBMCFunction (BMCModule &parent) :
            BMCFunction (parent) {}

        virtual void runOnFunction (Function &F);
    };

}



#endif
