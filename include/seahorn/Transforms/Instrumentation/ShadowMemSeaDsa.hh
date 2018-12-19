#ifndef __SHADOW_MEM_SEA_DSA__HH__
#define __SHADOW_MEM_SEA_DSA__HH__

#include "seahorn/config.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

#include "sea_dsa/Global.hh"
#include "sea_dsa/Graph.hh"

#include "boost/container/flat_set.hpp"

namespace llvm {
  class TargetLibraryInfo;
}

namespace seahorn {
class ShadowMemSeaDsa : public llvm::ModulePass {
  llvm::Constant *m_memLoadFn = nullptr;
  llvm::Constant *m_memStoreFn = nullptr;
  llvm::Constant *m_memUniqLoadFn = nullptr;
  llvm::Constant *m_memUniqStoreFn = nullptr;
  llvm::Constant *m_memShadowInitFn = nullptr;
  llvm::Constant *m_memShadowUniqInitFn = nullptr;

  llvm::Constant *m_memShadowArgInitFn = nullptr;
  llvm::Constant *m_memShadowUniqArgInitFn = nullptr;

  llvm::Constant *m_argRefFn = nullptr;
  llvm::Constant *m_argModFn = nullptr;
  llvm::Constant *m_argNewFn = nullptr;

  llvm::Constant *m_markIn = nullptr;
  llvm::Constant *m_markOut = nullptr;
  llvm::Constant *m_markUniqIn = nullptr;
  llvm::Constant *m_markUniqOut = nullptr;

  sea_dsa::GlobalAnalysis *m_dsa = nullptr;


  llvm::TargetLibraryInfo *m_tli = nullptr;

  using ShadowsMap =
      llvm::DenseMap<const sea_dsa::Node *,
                     llvm::DenseMap<unsigned, llvm::AllocaInst *>>;
  using NodeIdMap = llvm::DenseMap<const sea_dsa::Node *, unsigned>;

  ShadowsMap m_shadows;
  NodeIdMap m_node_ids;
  unsigned m_max_id = 0;
  llvm::Type *m_Int32Ty;

  using NodeSet = boost::container::flat_set<const sea_dsa::Node *>;
  using NodeSetMap = llvm::DenseMap<const llvm::Function *, NodeSet>;
  NodeSetMap m_readList;
  NodeSetMap m_modList;

  void declareFunctions(llvm::Module &M);
  llvm::AllocaInst *allocaForNode(const sea_dsa::Node *n, unsigned offset);
  unsigned getId(const sea_dsa::Node *n, unsigned offset);
  unsigned getOffset(const sea_dsa::Cell &c);

  unsigned getId(const sea_dsa::Cell &c) {
    return getId(c.getNode(), getOffset(c));
  }
  llvm::AllocaInst *allocaForNode(const sea_dsa::Cell &c) {
    return allocaForNode(c.getNode(), getOffset(c));
  }

  /// compute read/modified information per function
  void computeReadMod();
  void updateReadMod(llvm::Function &F, NodeSet &readSet, NodeSet &modSet);

  bool isRead(const sea_dsa::Cell &c, const llvm::Function &f);
  bool isRead(const sea_dsa::Node *n, const llvm::Function &f);
  bool isModified(const sea_dsa::Cell &c, const llvm::Function &f);
  bool isModified(const sea_dsa::Node *n, const llvm::Function &f);

public:
  static char ID;

  ShadowMemSeaDsa() : llvm::ModulePass(ID) {}

  virtual bool runOnModule(llvm::Module &M);
  virtual bool runOnFunction(llvm::Function &F);

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual llvm::StringRef getPassName() const { return "ShadowMemSeaDsa"; }
};
} // namespace seahorn
#endif
