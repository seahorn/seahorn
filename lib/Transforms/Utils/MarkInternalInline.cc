#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

using namespace llvm;

namespace seahorn
{
  /// marks all internal functions with AlwaysInline attribute
  struct MarkInternalInline : public ModulePass
  {
    static char ID;
    MarkInternalInline () : ModulePass (ID) {}
    
    void getAnalysisUsage (AnalysisUsage &AU) const
    {AU.setPreservesAll ();}
    
    bool runOnModule (Module &M)
    {
      for (Function &F : M)
        if (!F.isDeclaration () && F.hasLocalLinkage ())
          F.addFnAttr (Attribute::AlwaysInline);
      return true;
    }
    
  };
  
  char MarkInternalInline::ID = 0;
  
  Pass *createMarkInternalInlinePass () {return new MarkInternalInline ();}
  
}
