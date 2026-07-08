#include "seahorn/SeaNewPmPasses.hh"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

namespace
{
  class StripLifetime: public ModulePass 
  {
  public:
    static char ID;
    StripLifetime () : ModulePass (ID) {} 

    void getAnalysisUsage (AnalysisUsage &AU) const override
    {AU.setPreservesAll ();}
    
    bool runOnModule (Module &M) override
    {
      std::vector<std::string> voidFnNames = 
        {"llvm.lifetime.start", "llvm.lifetime.end" };
      
      for (auto &name : voidFnNames)
      {
        Function *fn = M.getFunction (name);
        if (!fn) continue;
        
        while (!fn->use_empty ())
        {
          CallInst *ci = cast<CallInst> (fn->user_back ());
          Value *last = *(ci->arg_end() - 1);
          ci->eraseFromParent ();
          RecursivelyDeleteTriviallyDeadInstructions (last);
        }
      }
      return true;
    }
    
  };
  char StripLifetime::ID = 0;
}
namespace seahorn
{
  Pass * createStripLifetimePass () {return new StripLifetime ();}

  llvm::PreservedAnalyses
  StripLifetimeNewPass::run(llvm::Module &M, llvm::ModuleAnalysisManager &) {
    return StripLifetime().runOnModule(M) ? llvm::PreservedAnalyses::none()
                                          : llvm::PreservedAnalyses::all();
  }
}

static llvm::RegisterPass<StripLifetime> Y ("strip-lifetime",
                                            "Remove llvm.lifetime instrinsics");


