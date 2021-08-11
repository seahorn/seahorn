#pragma once

#include "seahorn/config.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#ifdef HAVE_CLAM
#include "llvm/ADT/DenseSet.h"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/OperationalSemantics.hh"

#include "clam/Clam.hh"

namespace clam {
class CfgBuilder;
class LinConsToExprImpl;
} //end namespace clam
#endif

namespace seahorn {

/// LLVM pass that loads Crab invariants into a Horn Solver
class LoadCrabPass : public llvm::ModulePass {
public:
  static char ID;

  LoadCrabPass() : llvm::ModulePass(ID) {}
  virtual ~LoadCrabPass() {}

  virtual bool runOnModule(llvm::Module &M);
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual llvm::StringRef getPassName() const { return "LoadCrab"; }
};


#ifdef HAVE_CLAM
class HornifyModule;
/// Loads Crab invariants into a Horn Solver
class LoadCrab {
  const clam::ClamGlobalAnalysis &m_clam;
  const clam::AnalysisParams &m_params;
  HornifyModule &m_hm;

  Expr CrabInvToExpr(llvm::BasicBlock &B, const clam::CfgBuilder *cfgBuilder,
		     const llvm::DenseSet<const llvm::Value*> *live);
  
public:
  LoadCrab(const clam::ClamGlobalAnalysis &clam,
	   const clam::AnalysisParams &params,
	   HornifyModule &hm);
  ~LoadCrab() = default;
  LoadCrab(const LoadCrab &o) = delete;
  bool runOnModule(llvm::Module &M);
};

class LinConsToExpr {
public:

  LinConsToExpr(const clam::CfgBuilder *cfgBuilder, const llvm::Function &func);
  ~LinConsToExpr();

  /* Convert a crab linear expression into Expr using crab's semantics */
  expr::Expr toExpr(const clam::lin_cst_t &cst, expr::ExprFactory &efac,
		    const llvm::DenseSet<const llvm::Value*> *live = nullptr);
  /* Convert a crab linear expression into Expr using sem's semantics */
  expr::Expr toExpr(const clam::lin_cst_t &cst,
		    OperationalSemantics &sem, OpSemContext &semCtx,
		    const llvm::DenseSet<const llvm::Value*> *live = nullptr);

private:
  std::unique_ptr<clam::LinConsToExprImpl> m_impl;
};

class DisjunctiveLinConsToExpr {
public:

  DisjunctiveLinConsToExpr(const clam::CfgBuilder *cfgBuilder, const llvm::Function &func);
  ~DisjunctiveLinConsToExpr();
  
  /* Convert a crab disjunction of linear constraints into Expr using
     crab's semantics */
  Expr toExpr(const clam::disj_lin_cst_sys_t &csts, ExprFactory &efac,
	      const llvm::DenseSet<const llvm::Value*> *live = nullptr);  
  
private:
  std::unique_ptr<clam::LinConsToExprImpl> m_e;
};
#endif /* HAVE_CLAM */

} // namespace seahorn
