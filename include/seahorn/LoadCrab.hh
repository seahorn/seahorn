#pragma once

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/config.h"
#include "ufo/Expr.hpp"

#ifdef HAVE_CRAB_LLVM
#include "crab_llvm/crab_cfg.hh"
#include "seahorn/LegacyOperationalSemantics.hh"
#endif 

namespace seahorn
{

  /// Loads Crab invariants into a Horn Solver
  class LoadCrab: public llvm::ModulePass {
  public:
    static char ID;
    
    LoadCrab (): llvm::ModulePass(ID) {}
    virtual ~LoadCrab () {}
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (llvm::Function &F);
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual llvm::StringRef getPassName () const {return "LoadCrab";}
  };

}

#ifdef HAVE_CRAB_LLVM
namespace crab_llvm {
  class HeapAbstraction;
  class LinConsToExprImpl;
}

namespace seahorn {

  class LinConsToExpr {
  public:
    
    LinConsToExpr(crab_llvm::HeapAbstraction &heap_abs, const llvm::Function& f,
		  const expr::ExprVector &live);

    ~LinConsToExpr();

    /* Convert a crab linear expression into Expr using crab's semantics */
    expr::Expr toExpr(crab_llvm::lin_cst_t cst, expr::ExprFactory &efac);

    /* Convert a crab linear expression into Expr using sem's semantics */    
    expr::Expr toExpr(crab_llvm::lin_cst_t cst, LegacyOperationalSemantics& sem);
    
  private:
    crab_llvm::LinConsToExprImpl* m_impl;
  };
}
#endif 
  

