#pragma once

#include "seahorn/Expr/Expr.hh"
#include "seahorn/config.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#ifdef HAVE_CLAM
#include "clam/Clam.hh"
#include "seahorn/LegacyOperationalSemantics.hh"
#endif

namespace seahorn {

/// Loads Crab invariants into a Horn Solver
class LoadCrab : public llvm::ModulePass {
public:
  static char ID;

  LoadCrab() : llvm::ModulePass(ID) {}
  virtual ~LoadCrab() {}

  virtual bool runOnModule(llvm::Module &M);
  virtual bool runOnFunction(llvm::Function &F);
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual llvm::StringRef getPassName() const { return "LoadCrab"; }
};

} // namespace seahorn

#ifdef HAVE_CLAM
namespace clam {
class HeapAbstraction;
class LinConsToExprImpl;
} // namespace clam

namespace seahorn {

class LinConsToExpr {
public:
  LinConsToExpr(clam::HeapAbstraction &heap_abs, const llvm::Function &f,
                const expr::ExprVector &live);

  ~LinConsToExpr();

  /* Convert a crab linear expression into Expr using crab's semantics */
  expr::Expr toExpr(clam::lin_cst_t cst, expr::ExprFactory &efac);

  /* Convert a crab linear expression into Expr using sem's semantics */
  expr::Expr toExpr(clam::lin_cst_t cst, LegacyOperationalSemantics &sem);

private:
  clam::LinConsToExprImpl *m_impl;
};
} // namespace seahorn
#endif
