#ifndef __SHADOW_MEM_DSA__HH__
#define __SHADOW_MEM_DSA__HH__


#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/config.h"

#ifdef HAVE_DSA
#include "dsa/DataStructure.h"
#include "dsa/DSGraph.h"
#include "dsa/DSNode.h"

namespace seahorn
{
  using namespace llvm;
  
  class ShadowMemDsa : public llvm::ModulePass
  {
    Constant *m_memLoadFn;
    Constant *m_memStoreFn;
    Constant *m_memShadowInitFn;
    
    Constant *m_memShadowArgInitFn;
    
    Constant *m_argRefFn;
    Constant *m_argModFn;
    Constant *m_argNewFn;
    
    Constant *m_markIn;
    Constant *m_markOut;
    
    DataStructures *m_dsa;
    
    DenseMap<const DSNode*, AllocaInst*> m_shadows;
    DenseMap<const DSNode*, unsigned> m_node_ids;
    Type *m_Int32Ty;
    
    
    AllocaInst* allocaForNode (const DSNode *n);
    unsigned getId (const DSNode *n);
    
    
  public:
    static char ID;
    
    ShadowMemDsa () : llvm::ModulePass (ID)
    {}
    
    virtual bool runOnModule (llvm::Module &M);
    virtual bool runOnFunction (Function &F);
    
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "ShadowMemDsa";}
  };
  
}
#else
#include "llvm/Support/raw_os_ostream.h"

namespace seahorn
{
  using namespace llvm;
  class ShadowMemDsa : public llvm::ModulePass
  {
  public:
    static char ID;
    ShadowMemDsa () : llvm::ModulePass (ID) {}
    virtual bool runOnModule (llvm::Module &M)
    {
      errs () << "WARNING: Ignoring memory. Compiled without DSA library.\n";
      return false;
    }
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const
    {AU.setPreservesAll ();}
    virtual const char* getPassName () const {return "Stub-ShadowMemDsa";}
  };
}

#endif

#endif
