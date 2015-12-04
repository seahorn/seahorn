/* Externalize uses of functions whose address have been taken */
#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/ADT/SmallPtrSet.h"
#include "llvm/Support/Debug.h"

using namespace llvm;

namespace seahorn
{

  class ExternalizeAddressTakenFunctions : public ModulePass
  {
   public:
    
    static char ID;
    
    ExternalizeAddressTakenFunctions (): ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M) {
      
      bool Changed = false;
      for (auto &F: M) {
        
        // skip functions without a body
        if (F.isDeclaration () || F.empty ()) continue;
        
        if (F.hasAddressTaken ()) {
          // create function type
          const FunctionType *FTy = F.getFunctionType ();
          std::vector<llvm::Type*> ParamsTy (FTy->param_begin (), FTy->param_end ());
          Type *RetTy = F.getReturnType ();
          FunctionType *NFTy = FunctionType::get (RetTy, 
                                                  ArrayRef<llvm::Type*> (ParamsTy), 
                                                  FTy->isVarArg ());
          // create new function 
          Function *NF = Function::Create (NFTy, 
                                           GlobalValue::ExternalLinkage, 
                                           F.getName () + ".stub");
          NF->copyAttributesFrom(&F);
          F.getParent ()->getFunctionList ().insert(&F, NF);       
          
          // replace each use &foo with &foo_stub() where foo_stub is a
          // copy of foo but marked as external.
          Value::use_iterator UI = F.use_begin (), E = F.use_end ();
          for (; UI != E;)
          {
            Use &U = *UI;
            ++UI;
            User *FU = U.getUser();
            if (isa<BlockAddress>(FU))
              continue;
            
            if (isa<CallInst>(FU) || isa<InvokeInst>(FU)) {
              ImmutableCallSite CS(dyn_cast<Instruction>(FU));                        
             if (!CS.isCallee (&U)) {
               U.set (NF);
               Changed=true;
             }
            }
            
            if (!isa<CallInst>(FU) && !isa<InvokeInst>(FU)) {
              if (GlobalAlias *a = dyn_cast<GlobalAlias> (FU))
                //a->replaceUsesOfWithOnConstant (&F, NF, &U);
                a->setAliasee (NF);
              else if (Constant *c = dyn_cast<Constant> (FU)) 
                c->replaceUsesOfWithOnConstant (&F, NF, &U);
              else
                U.set (NF);
              Changed=true;
            }

          }
        }
      }
      
      return Changed;
    }
    
    void getAnalysisUsage (AnalysisUsage &AU) {
      AU.setPreservesAll ();
    }
    
  };

   char ExternalizeAddressTakenFunctions::ID = 0;

   Pass* createExternalizeAddressTakenFunctionsPass () {
     return new ExternalizeAddressTakenFunctions ();
   }
   
} // end namespace   
      


