/**
SeaHorn Verification Framework
Copyright (c) 2017 Arie Gurfinkel and Jorge Navas.
All Rights Reserved.

Released under a modified BSD license, please see license.txt for full
terms.
*/

#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Transforms/Utils/Local.h"
#include "seahorn/Transforms/Utils/Local.hh"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/TargetLibraryInfo.h"

using namespace llvm;

static cl::opt<bool>
KeepLibFn("keep-lib-fn",
          cl::desc("Do not strip external references to well-known library functions"),
          cl::init(false));

namespace
{
  class StripUselessDeclarations : public ModulePass
  {
    unsigned m_count;
    TargetLibraryInfo *m_tli;

  public:
    static char ID;
    StripUselessDeclarations () : ModulePass (ID), m_count(0), m_tli(nullptr) {}

    void getAnalysisUsage (AnalysisUsage &AU) const override
    {
      AU.addRequired<TargetLibraryInfoWrapperPass> ();
      AU.setPreservesAll ();
    }

    bool isUseless (Function &F) {
        auto name = F.getName ();
        if (name.startswith ("llvm.")) return false;
        if (name.startswith ("malloc") ||
            name.startswith ("calloc") ||
            name.startswith ("memset") ||
            name.startswith ("memcpy")) return false;

        if (name.startswith ("klee_")) return false;

        if (name.startswith ("seahorn.") ||
            name.startswith ("__seahorn") ||
            name.startswith ("verifier.") ||
	    name.startswith ("sea_dsa")) return false;

        if (name.startswith ("__VERIFIER")) return false;

        if (name.startswith ("__builtin")) return false;

        if (KeepLibFn) {
            if (!m_tli)
                m_tli = &getAnalysis<TargetLibraryInfoWrapperPass> ().getTLI(F);

            // known library function
            LibFunc libfn;
            if (m_tli->getLibFunc (name, libfn)) return false;
        }

        return true;

    }
    bool runOnModule (Module &M) override
    {
      for (auto &F : M)
      {
        if (F.isDeclaration ())
        {
            if (isUseless (F)) strip (F);
        }
        else
          stripAsm (F);
      }
      return true;
    }

    void strip (Function &F)
    {
      SmallVector<Value*, 16> args;
      SmallVector<CallBase*, 32> ToRemove;
      
      Value::use_iterator UI = F.use_begin (), E = F.use_end ();
      for (; UI != E;)
      {
        Use &U = *UI;
        ++UI;
        User *FU = U.getUser ();
        if (isa<BlockAddress> (FU)) continue;
	if (InvokeInst *II = dyn_cast<InvokeInst> (FU)) {
	  // Invoke instructions are terminators so if II is the
	  // terminator of its block then we don't touch it, otherwise
	  // the CFG won't be well-formed.
	  if (II->getParent()->getTerminator() == II) {
	    continue;
	  }
	}
        if (isa<CallInst> (FU) || isa<InvokeInst> (FU))
        {
          auto &CB = *cast<CallBase>(FU);
          if (!CB.isCallee (&U)) continue;

          // -- do not delete functions that take no arguments,
          // -- they are treated as non-deterministic anyhow
          if (CB.data_operands_empty ()) continue;

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
            Builder.SetInsertPoint (&CB);
            CallInst *call = Builder.CreateCall (&ndfn);
            call->setDebugLoc (CB.getDebugLoc ());

            // -- replace old call with nondet one
            CB.replaceAllUsesWith (call);
          }

          // -- push the old call instruction in the queue to be
          // -- removed. Otherwise, we might invalidate iterators when
          // -- calling RecursivelyDeleteTriviallyDeadInstructions.
          if (FU->use_empty ()) {
            ToRemove.push_back(&CB);
          }
        }
      }

      while (!ToRemove.empty()) {
        auto *CB = ToRemove.back();
        ToRemove.pop_back();
        args.insert(args.end(), CB->data_operands_begin(), CB->data_operands_end());
        CB->eraseFromParent();
        for (auto &a : args) {
          seahorn::RecursivelyDeleteTriviallyDeadInstructions(a);
        }
        args.clear();
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
          args.insert (args.end (), call->data_operands_begin (), call->data_operands_end ());

          if (!call->use_empty ())
          {
            std::string fName = "nondet.asm.";
            Function &ndfn = seahorn::createNewNondetFn (*F.getParent (),
                                                         *call->getType (),
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
