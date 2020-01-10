#pragma once

#include "seahorn/config.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#ifdef HAVE_DSA
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"
#include "dsa/DataStructure.h"

namespace seahorn {
using namespace llvm;

class LlvmDsaShadowMem : public llvm::ModulePass {
  Constant *m_memLoadFn;
  Constant *m_memStoreFn;
  Constant *m_memUniqLoadFn;
  Constant *m_memUniqStoreFn;
  Constant *m_memShadowInitFn;
  Constant *m_memShadowUniqInitFn;

  Constant *m_memShadowArgInitFn;
  Constant *m_memShadowUniqArgInitFn;

  Constant *m_argRefFn;
  Constant *m_argModFn;
  Constant *m_argNewFn;

  Constant *m_markIn;
  Constant *m_markOut;
  Constant *m_markUniqIn;
  Constant *m_markUniqOut;

  DataStructures *m_dsa;

  DenseMap<const DSNode *, AllocaInst *> m_shadows;
  DenseMap<const DSNode *, unsigned> m_node_ids;
  Type *m_Int32Ty;

  AllocaInst *allocaForNode(const DSNode *n);
  unsigned getId(const DSNode *n);

public:
  static char ID;

  LlvmDsaShadowMem() : llvm::ModulePass(ID) {}

  virtual bool runOnModule(llvm::Module &M);
  virtual bool runOnFunction(Function &F);

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual StringRef getPassName() const { return "LlvmDsaShadowMem"; }
};

} // namespace seahorn
#else
#include "llvm/Support/raw_os_ostream.h"

namespace seahorn {
using namespace llvm;

class LlvmDsaShadowMem : public llvm::ModulePass {
public:
  static char ID;
  LlvmDsaShadowMem() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M) {
    errs() << "WARNING: Ignoring memory. Compiled without DSA library.\n";
    return false;
  }
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll();
  }
  virtual StringRef getPassName() const { return "Stub-LlvmDsaShadowMem"; }
};
} // namespace seahorn
#endif
