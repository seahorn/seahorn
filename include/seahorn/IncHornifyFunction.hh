#ifndef FEASIBLEHORNIFYFUNCTION_H
#define FEASIBLEHORNIFYFUNCTION_H

#include "seahorn/HornifyFunction.hh"
#include "llvm/IR/Function.h"

#include "seahorn/LiveSymbols.hh"
#include "seahorn/UfoSymExec.hh"
#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"

namespace seahorn {
using namespace expr;
using namespace llvm;
using namespace ufo;

// Encoding to prove if a basic block is feasible. A block b is
// feasible if there is a path from the entry to b and from b to the
// exit block.
//
// Each predicate is augmented with n boolean flags where n is the
// number of blocks in the function.
//
// For each clause:
//      head(...,b1,...,1,...,bn) <- body (...,b1,...,bk,...,bn)
//      where bk is the Boolean flag corresponding to the destination block.
//
// Notes: this encoding is not intended to be used with
//        interprocedural encodings.
class IncHornifyFunction : public HornifyFunction {
  typedef llvm::DenseMap<const BasicBlock *, Expr> PredDeclMap;

  /// -- Cannot use the map from the parent (module)
  PredDeclMap m_bbPreds;

  /// File to write the debug info


protected:
  /// -- add predicate declaration for the given basic block
  const Expr declarePredicate(const BasicBlock &bb, const ExprVector &live);

  /// -- get predicate declaration for the given basic block
  const Expr bbPredicate(const BasicBlock &bb);

  /// -- extract infos from Basic Blocks
  std::string extractInfo(const BasicBlock &bb, unsigned crumb_var);

public:
  IncHornifyFunction(HornifyModule &parent, bool interproc = false)
      : HornifyFunction(parent, interproc) {}
};

class IncSmallHornifyFunction : public IncHornifyFunction {

public:
  IncSmallHornifyFunction(HornifyModule &parent, bool interproc = false)
      : IncHornifyFunction(parent, interproc) {}

  virtual void runOnFunction(Function &F);
};
}

#endif /* FEASIBLEHORNIFYFUNCTION_H */
