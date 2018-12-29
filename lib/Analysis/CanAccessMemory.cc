#include "seahorn/Analysis/CanAccessMemory.hh"

#include "llvm/IR/InstIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"
namespace seahorn
{
  using namespace llvm;
  
  char CanAccessMemory::ID = 0;
  
  bool CanAccessMemory::canAccess (const Function *f) const
  {return m_must.count (f) > 0 || m_may.count (f) > 0;}
  
  bool CanAccessMemory::runOnModule (Module &M)
  {
    LOG ("canmem", errs () << "Running may access memory analysis\n";);

    for (Function &F : M)
    {
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) 
      {
        Instruction *I = &*i;
        if (isa<LoadInst>(I) || isa<StoreInst>(I))
        {
          m_must.insert (&F);
          break;
        }
        if (const CallInst *CI = dyn_cast<CallInst> (I))
        {
          CallSite CS (const_cast<CallInst*> (CI));
          const Function *cf = CS.getCalledFunction ();
          if (cf && 
              ( cf->getName ().startswith ("llvm.memcpy") || 
                cf->getName ().startswith ("llvm.memmove") ||
                cf->getName ().startswith ("llvm.memset")))
          {
            m_must.insert (&F);
            break;
          }
        }
      }      
    }
        
    LOG ("canmem", errs () << "Must access to memory: ";
         for (auto v : m_must) errs () << v->getName () << ", ";
         errs () << "\n";);
    
    // -- no error function found at all
    if (m_must.empty ()) return false;
    
    CallGraph &CG = getAnalysis<CallGraphWrapperPass> ().getCallGraph ();
    for (auto it = scc_begin (&CG); !it.isAtEnd (); ++it)
    {
      auto &scc = *it;
      bool mark = false;
      
      // -- check if any of the functions in the scc calls something
      // -- that may access to memory
      for (CallGraphNode *cgn : scc)
      {
        for (auto &calls : *cgn)
          if (canAccess (calls.second->getFunction ()))
          {mark=true; break;}
      }
      if (mark)
      {
        for (auto *cgn : scc)
          if (cgn->getFunction ())
            m_may.insert (cgn->getFunction ());
      }
    }
    
    LOG ("canmem", errs () << "May access to memory: ";
         for (auto v : m_may) errs () << v->getName () << ", ";
         errs () << "\n";);
    
      
    return false;
  }
  
  void CanAccessMemory::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  }
}

static llvm::RegisterPass<seahorn::CanAccessMemory>
X ("mark-mem-access", "Mark functions that can access to memory");
