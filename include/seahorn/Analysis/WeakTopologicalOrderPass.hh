#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "seahorn/Analysis/WeakTopologicalOrder.hh"

using namespace llvm;

namespace seahorn {

/// Construct weak topological order of a CFG of a function
class WeakTopologicalOrderPass : public llvm::FunctionPass {
  typedef WeakTopoOrder<llvm::Function> wto_t;

  wto_t m_wto;

public:
  typedef typename wto_t::const_iterator const_iterator;

  static char ID;

  WeakTopologicalOrderPass() : FunctionPass(ID), m_wto() {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;

  virtual bool runOnFunction(llvm::Function &F);

  const_iterator begin() const { return m_wto.begin(); }
  const_iterator end() const { return m_wto.end(); }

  // TODO: wto_t has more methods that should be exposed here,
  // specially those to iterate over the nested components of a
  // given basic block.

  virtual StringRef getPassName() const { return "WeakTopologicalOrder"; }
};

} // namespace seahorn
