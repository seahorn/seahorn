#ifndef __SHADOW_MEM_SEA_DSA__HH__
#define __SHADOW_MEM_SEA_DSA__HH__

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "seahorn/config.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/Global.hh"

#include "boost/container/flat_set.hpp"

using namespace seahorn::dsa;

namespace seahorn
{
  using namespace llvm;

  class ShadowMemSeaDsa : public llvm::ModulePass
  {
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
    
    GlobalAnalysis *m_dsa;
    
    DenseMap<const Node*, DenseMap<unsigned, AllocaInst*> > m_shadows;
    DenseMap<const Node*, unsigned> m_node_ids;
    unsigned m_max_id;
    Type *m_Int32Ty;
    
    typedef boost::container::flat_set<const Node*> NodeSet;
    DenseMap<const Function *, NodeSet> m_readList;
    DenseMap<const Function *, NodeSet > m_modList;
    
    
    void declareFunctions (llvm::Module &M);
    AllocaInst* allocaForNode (const Node *n, unsigned offset);
    unsigned getId (const Node *n, unsigned offset);
    unsigned getOffset (const Cell &c);
    
    unsigned getId (const Cell &c)
    { return getId (c.getNode(), getOffset (c)); }
    AllocaInst* allocaForNode (const Cell &c)
    { return allocaForNode (c.getNode (), getOffset (c)); }
    
    /// compute read/modified information per function
    void computeReadMod ();
    void updateReadMod (Function &F, NodeSet &readSet, NodeSet &modSet);
    
    bool isRead (const Cell &c, const Function &f);
    bool isRead (const Node* n, const Function &f);
    bool isModified (const Cell &c, const Function &f);
    bool isModified (const Node *n, const Function &f);
    
  public:
    static char ID;
    
    ShadowMemSeaDsa () : llvm::ModulePass (ID), m_max_id(0)
    {}
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "ShadowMemSeaDsa";}
  }; 
}
#endif
