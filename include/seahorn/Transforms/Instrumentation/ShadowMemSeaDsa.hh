#ifndef __SHADOW_MEM_SEA_DSA__HH__
#define __SHADOW_MEM_SEA_DSA__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "seahorn/config.h"

#include "sea_dsa/Graph.hh"
#include "sea_dsa/Global.hh"

#include "boost/container/flat_set.hpp"

namespace seahorn
{
  class ShadowMemSeaDsa : public llvm::ModulePass
  {
    llvm::Constant *m_memLoadFn;
    llvm::Constant *m_memStoreFn;
    llvm::Constant *m_memUniqLoadFn;
    llvm::Constant *m_memUniqStoreFn;
    llvm::Constant *m_memShadowInitFn;
    llvm::Constant *m_memShadowUniqInitFn;
    
    llvm::Constant *m_memShadowArgInitFn;
    llvm::Constant *m_memShadowUniqArgInitFn;
    
    llvm::Constant *m_argRefFn;
    llvm::Constant *m_argModFn;
    llvm::Constant *m_argNewFn;
    
    llvm::Constant *m_markIn;
    llvm::Constant *m_markOut;
    llvm::Constant *m_markUniqIn;
    llvm::Constant *m_markUniqOut;
    
    sea_dsa::GlobalAnalysis *m_dsa;
    
    llvm::DenseMap<const sea_dsa::Node*,
		   llvm::DenseMap<unsigned, llvm::AllocaInst*> > m_shadows;
    llvm::DenseMap<const sea_dsa::Node*, unsigned> m_node_ids;
    unsigned m_max_id;
    llvm::Type *m_Int32Ty;
    
    typedef boost::container::flat_set<const sea_dsa::Node*> NodeSet;
    llvm::DenseMap<const llvm::Function *, NodeSet> m_readList;
    llvm::DenseMap<const llvm::Function *, NodeSet > m_modList;
    
    
    void declareFunctions (llvm::Module &M);
    llvm::AllocaInst* allocaForNode (const sea_dsa::Node *n, unsigned offset);
    unsigned getId (const sea_dsa::Node *n, unsigned offset);
    unsigned getOffset (const sea_dsa::Cell &c);
    
    unsigned getId (const sea_dsa::Cell &c)
    { return getId (c.getNode(), getOffset (c)); }
    llvm::AllocaInst* allocaForNode (const sea_dsa::Cell &c)
    { return allocaForNode (c.getNode (), getOffset (c)); }
    
    /// compute read/modified information per function
    void computeReadMod ();
    void updateReadMod (llvm::Function &F, NodeSet &readSet, NodeSet &modSet);
    
    bool isRead (const sea_dsa::Cell &c, const llvm::Function &f);
    bool isRead (const sea_dsa::Node* n, const llvm::Function &f);
    bool isModified (const sea_dsa::Cell &c, const llvm::Function &f);
    bool isModified (const sea_dsa::Node *n, const llvm::Function &f);
    
  public:
    static char ID;
    
    ShadowMemSeaDsa () : llvm::ModulePass (ID), m_max_id(0) {}
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (llvm::Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "ShadowMemSeaDsa";}
  }; 
}
#endif
