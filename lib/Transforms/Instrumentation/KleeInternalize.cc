/**
SeaHorn Verification Framework
Copyright (c) 2016 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified BSD license, please see license.txt for full
terms.

DM-0002198
*/

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"

#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>
#include <set>
#include <string>
using namespace llvm;

// APIFile - A file which contains a list of symbols that should not be marked
// external.
static cl::opt<std::string>
APIFile("klee-internalize-public-api-file", cl::value_desc("filename"),
        cl::desc("A file containing list of symbol names to preserve"));

// APIList - A list of symbols that should not be marked internal.
static cl::list<std::string>
APIList("klee-internalize-public-api-list", cl::value_desc("list"),
        cl::desc("A list of symbol names to preserve"),
        cl::CommaSeparated);


namespace
{
  /** 
   * Internalizes external definitions by providing stubs and
   * definitions.
   */
  class KleeInternalize : public ModulePass
  {
    std::set<std::string> m_externalNames;
    
    const DataLayout *m_dl;
    TargetLibraryInfo *m_tli;
    IntegerType *m_intptrTy;

    Function* m_assertFailFn;
    Function* m_kleeAssumeFn;
    Function* m_kleeMkSymbolicFn;

    Value *m_failed;
    Value *m_builtin;
    
    void declareKleeFunctions (Module &M)
    {
      LLVMContext &C = M.getContext ();
      m_dl = &(getAnalysis<DataLayoutPass>().getDataLayout());

      m_intptrTy = m_dl->getIntPtrType (C, 0);

      Type *voidTy = Type::getVoidTy (C);
      Type *i8PtrTy = Type::getInt8PtrTy (C);
      Type *i32Ty = Type::getInt32Ty (C);
      
      m_assertFailFn = cast<Function> (M.getOrInsertFunction ("__assert_fail",
                                                              voidTy,
                                                              i8PtrTy, i8PtrTy,
                                                              i32Ty,
                                                              i8PtrTy,
                                                              NULL));
                                                              
      m_kleeAssumeFn = cast<Function> (M.getOrInsertFunction ("klee_assume",
                                                              voidTy,
                                                              m_intptrTy,
                                                              NULL));
      
      m_kleeMkSymbolicFn = cast<Function> (M.getOrInsertFunction ("klee_make_symbolic",
                                                                  voidTy,
                                                                  i8PtrTy,
                                                                  m_intptrTy,
                                                                  i8PtrTy,
                                                                  NULL));


      m_externalNames.insert (m_assertFailFn->getName ());
      m_externalNames.insert (m_kleeAssumeFn->getName ());
      m_externalNames.insert (m_kleeMkSymbolicFn->getName ());
      
      CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
      if (CallGraph *cg = cgwp ? &cgwp->getCallGraph () : nullptr)
      {
        cg->getOrInsertFunction (m_assertFailFn);
        cg->getOrInsertFunction (m_kleeAssumeFn);
        cg->getOrInsertFunction (m_kleeMkSymbolicFn);
      }
    }

    bool shouldInternalize (const GlobalValue &GV)
    {
      if (!GV.isDeclaration()) return false;
      if (GV.getName().startswith ("llvm.")) return false;

      if (!m_tli) m_tli = &getAnalysis<TargetLibraryInfo> ();

      // -- known library function 
      LibFunc::Func F;
      if (m_tli->getLibFunc (GV.getName(), F)) return false;
          
      if (m_externalNames.count (GV.getName())) return false;
      
      return true;
    }
    
    void defineFunction (Function &F)
    {
      errs () << "Defining: " << F.getName () << "\n";
      BasicBlock *bb = BasicBlock::Create (F.getContext(), "entry", &F);
      IRBuilder<> Builder (bb);
      
      Type *retTy = F.getReturnType ();
      if (retTy->isVoidTy ())
        Builder.CreateRetVoid ();
      else
      {
        uint64_t storeSzInBits = m_dl->getTypeStoreSizeInBits(retTy);
        Type* storeTy = Type::getIntNTy(F.getContext(),storeSzInBits);

        AllocaInst *v = Builder.CreateAlloca (retTy);
        ConstantInt *sz = Builder.getIntN (m_intptrTy->getBitWidth(), 
                                           storeSzInBits  / 8);
        Value *fname = Builder.CreateGlobalString (F.getName ());

        CallInst *mksym =
          Builder.CreateCall3 (m_kleeMkSymbolicFn,
                               Builder.CreateBitCast (v, Builder.getInt8PtrTy ()),
                               sz,
                               Builder.CreateConstGEP2_32 (fname, 0, 0));

        Value *retValue = Builder.CreateLoad (v);

	// TODO: update callgraph
        Builder.CreateRet (retValue);
      }
    }
    
    void LoadFile (const char *fname)
    {
      std::ifstream In(fname);
      if (!In.good()) {
        errs () << "WARNING: Could not load file '" << fname
                << "'! Continuing as if it is empty.\n";
        return;
      }
      while (In)
      {
        std::string Symbol;
        In >> Symbol;
        if (!Symbol.empty ())
          m_externalNames.insert (Symbol);
      }
    }
  public:
    static char ID;
    KleeInternalize () : ModulePass (ID), m_dl(nullptr), m_tli(nullptr)
    {
      if (!APIFile.empty ())
        LoadFile (APIFile.c_str ());
      m_externalNames.insert (APIList.begin (), APIList.end ());

      // functions that are replaced by internalizer
      m_externalNames.insert ("verifier.assume");
      m_externalNames.insert ("verifier.assume.not");
      m_externalNames.insert ("seahorn.fail");
      m_externalNames.insert ("verifier.error");
    }

    void getAnalysisUsage (AnalysisUsage &AU) const override
    {
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.setPreservesAll ();
    }

    bool runOnModule (Module &M)
    {
      declareKleeFunctions(M);

      for (Function &F : M)
      {
        if (shouldInternalize (F)) defineFunction (F);
        else if (!F.isDeclaration()) runOnFunction (F);
      }
      return true;
    }


    bool runOnFunction (Function &F)
    {
      errs() << "Processing: " << F.getName () << "\n";
      Value *fname = nullptr;
      LLVMContext &C = F.getContext();
      IRBuilder<> Builder (C);
      SmallVector<Instruction*, 16> killList;
      for (BasicBlock &bb : F)
      {
        for (Instruction &inst : bb)
        {
          if (!isa<CallInst> (inst) && !isa<InvokeInst> (inst)) continue;
          CallSite CS (&inst);
          Function *fn = CS.getCalledFunction();
          if (!fn) continue;

          CallInst *ninst = nullptr;
          Builder.SetInsertPoint (&inst);
          
          if (fn->getName().equals ("verifier.assume"))
          {
            ninst = Builder.CreateCall (m_kleeAssumeFn,
                                        Builder.CreateZExtOrTrunc (CS.getArgument (0),
                                                                   m_intptrTy));
          }
          else if (fn->getName().equals ("verifier.assume.not"))
          {
            ninst = Builder.CreateCall (m_kleeAssumeFn,
                                        Builder.CreateZExtOrTrunc
                                        (Builder.CreateNot (CS.getArgument (0)),
                                         m_intptrTy));
          }
          else if (fn->getName().equals ("seahorn.fail") ||
                   fn->getName().equals ("verifier.error"))
          {
            Value *nullV = ConstantPointerNull::get (Builder.getInt8PtrTy ());
            // TODO: extract line number info from inst
            if (!fname)
              fname = Builder.CreateGlobalString (F.getName ());
            ninst = Builder.CreateCall4 (m_assertFailFn,
                                         Builder.CreateGlobalStringPtr ("FAILED"),
                                         Builder.CreateGlobalStringPtr ("__builtin.c"),
                                         Builder.getInt32 (0),
                                         Builder.CreateConstGEP2_32 (fname, 0, 0));
            
          }
          
          if (ninst)
          {
            ninst->setDebugLoc (inst.getDebugLoc ());
            killList.push_back (&inst);
            // TODO: update callgraph
          }
          
        }
      }

      for (Instruction* i : killList)
      {
        i->eraseFromParent();
      }
      
      return true;
    }
  };

  char KleeInternalize::ID = 0;
}

namespace seahorn
{
  Pass *createKleeInternalizePass() { return new KleeInternalize(); }
}

static llvm::RegisterPass<KleeInternalize> Y ("klee-internalize-pass",
                                              "Internalize external definitions for Klee");
