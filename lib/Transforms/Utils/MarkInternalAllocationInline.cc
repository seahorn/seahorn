#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/CallSite.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/ADT/SmallSet.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

static llvm::cl::opt<unsigned int>
AllocInlineLevels("horn-inline-alloc-levels",
                  llvm::cl::desc ("Inline up to N levels of callers of functions that allocate memory"),
                  llvm::cl::init (1));

namespace seahorn
{
  /// Mark all functions that allocate or reallocate memory with
  /// AlwaysInline attribute
  struct MarkInternalAllocationInline : public ModulePass
  {
    static char ID;
    MarkInternalAllocationInline () : ModulePass (ID) {}
    
    void getAnalysisUsage (AnalysisUsage &AU) const {
      AU.setPreservesAll ();
      AU.addRequired<llvm::TargetLibraryInfo>();
    }
    
    bool markIfAllocationFn (Function& F,  const TargetLibraryInfo* TLI) {
      for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
        Instruction *I = &*i;
        if (CallInst *CI = dyn_cast<CallInst> (I)) {
          if (isAllocationFn (CI, TLI, true)) {
            F.addFnAttr (Attribute::AlwaysInline);
            errs () << F.getName () << " marked as internal (level=1)\n";
            return true;
          }
        }
      }
      return false;
    }

    bool markTransitivelyAllocationFn (Function& F,  unsigned int level, 
                                       SmallSet<Function*, 32>& AllocFn) {

      for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
        Instruction *I = &*i;
        if (CallInst *CI = dyn_cast<CallInst> (I)) {
          CallSite CS (CI);
          if (CS.getCalledFunction () && AllocFn.count (CS.getCalledFunction ()) > 0){
            F.addFnAttr (Attribute::AlwaysInline);
            AllocFn.insert (&F);
            errs () << F.getName () << " marked as internal (level=" << level << ")\n";
            return true;
          }
        }
      }
      return false;
    }

    bool runOnModule (Module &M) {

      if (AllocInlineLevels < 1 || M.empty ()) return false;

      const TargetLibraryInfo* TLI = &getAnalysis<TargetLibraryInfo>();
      bool Change = false;
      
      SmallSet<Function*, 32> AllocFn;
      for (Function &F : M) {
        if (!F.isDeclaration () && F.hasLocalLinkage ()) {
          if (markIfAllocationFn (F, TLI)) {
            AllocFn.insert (&F);
            Change = true;
          }
        }
      }

      if (!Change) return false;

      for (unsigned int l=1; l <= AllocInlineLevels; l++) {
        SmallSet<Function*, 32> TmpAllocFn (AllocFn);
        Change = false;
        for (Function &F : M) { 
          if (!F.isDeclaration () && F.hasLocalLinkage ())
            if (!(TmpAllocFn.count (&F) > 0))
              Change |= markTransitivelyAllocationFn (F, l, TmpAllocFn);
        }
        if (!Change) break;
        AllocFn.insert (TmpAllocFn.begin (), TmpAllocFn.end ());
      }  
      return true;
    }
    
  };
  
  char MarkInternalAllocationInline::ID = 0;
  
  Pass *createMarkInternalAllocationInlinePass () 
  {return new MarkInternalAllocationInline ();}
  
}
