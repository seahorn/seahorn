#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/Local.h"
#include "seahorn/Transforms/Utils/Local.hh"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/IRBuilder.h"

#include "llvm/Support/raw_ostream.h"
  
using namespace llvm;

namespace
{
  class StripUselessDeclarations : public ModulePass
  {
    unsigned m_count;
  public:
    static char ID;
    StripUselessDeclarations () : ModulePass (ID), m_count(0) {}

    void getAnalysisUsage (AnalysisUsage &AU) const override
    {AU.setPreservesAll ();}

    bool runOnModule (Module &M) override
    {
      for (auto &F : M)
      {
        if (F.isDeclaration ())
        {
          auto name = F.getName ();
          if (name.startswith ("llvm.")) continue;
          if (name.startswith ("malloc") ||
              name.startswith ("calloc") ||
              name.startswith ("memset") ||
              name.startswith ("memcpy")) continue;

          if (name.startswith ("klee_")) continue;

          if (name.startswith ("seahorn.") ||
              name.startswith ("verifier.")) continue;

          if (name.startswith ("__VERIFIER")) continue;

          if (name.startswith ("__builtin")) continue;
        
          strip (F);
        }
        else
          stripAsm (F);
      }
      return true;
    }

    void strip (Function &F)
    {
      SmallVector<Value*, 16> args;
      
      Value::use_iterator UI = F.use_begin (), E = F.use_end ();
      for (; UI != E;)
      {
        Use &U = *UI;
        ++UI;
        User *FU = U.getUser ();
        if (isa<BlockAddress> (FU)) continue;
        if (isa<CallInst> (FU) || isa<InvokeInst> (FU))
        {
          CallSite CS (dyn_cast<Instruction> (FU));
          if (!CS.isCallee (&U)) continue;

          // -- do not delete functions that take no arguments,
          // -- they are treated as non-deterministic anyhow
          if (CS.arg_empty ()) continue;
          
          if (!F.getReturnType ()->isVoidTy ())
          {
            // insert call to nondet fn
            std::string newName ("verifier.nondet.stripextern.");
            newName += F.getName ();
            newName += ".";
            
            Function &ndfn = seahorn::createNewNondetFn (*F.getParent (),
                                                         *F.getReturnType (), 1,
                                                         newName);
            IRBuilder<> Builder (F.getContext ());
            Builder.SetInsertPoint (CS.getInstruction ());
            CallInst *call = Builder.CreateCall (&ndfn);
            call->setDebugLoc (CS.getInstruction ()->getDebugLoc ());
            
            // -- replace old call with nondet one
            CS.getInstruction ()->replaceAllUsesWith (call);
          }
          
          // -- delete the old call instruction
          if (FU->use_empty ())
          {
            args.insert (args.end (), CS.arg_begin (), CS.arg_end ());
            CS.getInstruction ()->eraseFromParent ();
            for (auto &a : args)
              seahorn::RecursivelyDeleteTriviallyDeadInstructions (a);
            args.clear ();
          }
        }
      }
    }
    
    void stripAsm (Function &F)
    {
      SmallVector<CallInst*, 8> dead;
      SmallVector<Value*, 16> args;
      for (auto &bb : F)
      {
        for (auto &inst : bb)
        {
          if (CallInst *call = dyn_cast<CallInst> (&inst))
          {
            if (call->isInlineAsm ())
            {
              dead.push_back (call);
            }
          }
        }
        
        for (auto *call : dead)
        {
          CallSite CS(call);
          args.insert (args.end (), CS.arg_begin (), CS.arg_end ());
          
          if (!call->use_empty ())
          {
            std::string fName = "nondet.asm.";
            Function &ndfn = seahorn::createNewNondetFn (*F.getParent (),
                                                         *CS.getInstruction()->getType (),
                                                         m_count++,
                                                         fName);
            IRBuilder<> Builder (F.getContext ());
            Builder.SetInsertPoint (call);
            CallInst *nCall = Builder.CreateCall (&ndfn);
            nCall->setDebugLoc (call->getDebugLoc ());
            call->replaceAllUsesWith (nCall);
          }
          
          call->eraseFromParent ();
          for (auto &a : args)
            seahorn::RecursivelyDeleteTriviallyDeadInstructions (a);
          args.clear ();
        }
        dead.clear ();
      }
    }
    
  };
  char StripUselessDeclarations::ID = 0;
  
}

namespace seahorn
{
  Pass *createStripUselessDeclarationsPass ()
  {return new StripUselessDeclarations ();}
}

static llvm::RegisterPass<StripUselessDeclarations> X ("strip-useless-decls",
                                                       "Replace declarations by nondet");


