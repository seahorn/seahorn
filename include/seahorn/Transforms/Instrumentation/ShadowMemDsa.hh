#ifndef __SHADOW_MEM_DSA__HH__
#define __SHADOW_MEM_DSA__HH__

#include "llvm/Pass.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Constants.h"
#include "seahorn/config.h"

#include "ufo/Expr.hpp"

#include <queue>

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
    virtual StringRef getPassName () const {return "ShadowMemDsa";}
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
    virtual StringRef getPassName () const {return "Stub-ShadowMemDsa";}
  };
  
  class StripShadowMem: public llvm::ModulePass
  {
  public:
    static char ID;
    StripShadowMem () : llvm::ModulePass (ID) {}
    virtual bool runOnModule (llvm::Module &M)
    {
      errs () << "WARNING: Ignoring memory. Compiled without DSA library.\n";
      return false;
    }
    virtual void getAnalysisUsage (llvm::AnalysisUsage &AU) const
    {AU.setPreservesAll ();}
    virtual StringRef getPassName () const {return "Stub-StripShadowMem";}
  };
}
#endif
namespace seahorn
{
  namespace shadow_dsa
  {
    using namespace llvm;

    /// extracts unique scalar from a call to shadow.mem functions
    inline const Value *extractUniqueScalar (ImmutableCallSite cs)
    {
      if (cs.getCalledFunction()->getName().equals("shadow.mem.global.init")) return nullptr;
      assert (cs.arg_size () > 0);
      // -- last argument
      const Value *v = cs.getArgument (cs.arg_size () - 1);
       
      if (const Instruction *inst = dyn_cast<Instruction> (v))
      {
        assert (inst);
        return inst->isCast () ? inst->getOperand (0) : inst;
      }
      else if (const ConstantPointerNull *c = dyn_cast<ConstantPointerNull> (v))
        return nullptr;
      else if (const ConstantExpr *c = dyn_cast<ConstantExpr> (v))
        return c->getOperand (0);
       
      return v;
    }
  
    inline int64_t getShadowId (const ImmutableCallSite &cs)
    {
      assert (cs.arg_size () > 0);
      
      if (const ConstantInt *id = dyn_cast<ConstantInt> (cs.getArgument (0)))
        return id->getZExtValue ();
      
      return -1;
    }

    /// variable to represent start of a memory region with a given id
    inline expr::Expr memStartVar (unsigned id, expr::Expr sort)
    {
      using namespace expr;
      ExprFactory &efac = sort->efac ();
      return bind::mkConst
        (variant::variant (id, mkTerm<std::string> ("mem_start", efac)), sort);
    }
    
    /// variable to represent end of a memory region with a given id
    inline expr::Expr memEndVar (unsigned id, expr::Expr sort)
    {
      using namespace expr;
      ExprFactory &efac = sort->efac ();
      return bind::mkConst
        (variant::variant (id, mkTerm<std::string> ("mem_end", efac)), sort);
    }
    
    
    inline bool isShadowMem (const Value &V, const Value **out)
    {
       
      // work list
      std::queue<const Value *> wl;
      llvm::DenseSet<const Value *> visited;
       
      wl.push (&V);
      while (!wl.empty ())
      {
        const Value *val = wl.front ();
        wl.pop ();

        if (visited.count(val) > 0)
          continue;
        visited.insert(val);
         
        if (const CallInst *ci = dyn_cast<const CallInst> (val))
        {
          if (const Function *fn = ci->getCalledFunction ())
          {
            if (!fn->getName ().startswith ("shadow.mem")) return false;
            if (out) *out = extractUniqueScalar (ci);
            return true;
          }
           
          return false;
        }
        else if (const PHINode *phi = dyn_cast<const PHINode> (val))
        {
          for (unsigned i = 0; i < phi->getNumIncomingValues (); ++i)
            wl.push (phi->getIncomingValue (i));
        }
        else if (const SelectInst *gamma = dyn_cast<const SelectInst> (val))
        {
          if (gamma->getName().startswith("seahorn.gsa")) {
            wl.push (gamma->getTrueValue());
            wl.push (gamma->getFalseValue());
          }
          else return false;
        }
        else return false;
      }
       
      assert (0);
      return false;
    }
  }
}
#endif
