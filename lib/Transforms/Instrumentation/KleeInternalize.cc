/**
SeaHorn Verification Framework
Copyright (c) 2017 Arie Gurfinkel and Jorge Navas.
All Rights Reserved.

Released under a modified BSD license, please see license.txt for full
terms.
*/

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"

#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"

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
      m_dl = &M.getDataLayout();

      m_intptrTy = m_dl->getIntPtrType (C, 0);

      Type *voidTy = Type::getVoidTy (C);
      Type *i8PtrTy = Type::getInt8PtrTy (C);
      Type *i32Ty = Type::getInt32Ty (C);

      m_assertFailFn = cast<Function> (M.getOrInsertFunction ("__assert_fail",
                                                              voidTy,
                                                              i8PtrTy, i8PtrTy,
                                                              i32Ty,
                                                              i8PtrTy));

      m_kleeAssumeFn = cast<Function> (M.getOrInsertFunction ("klee_assume",
                                                              voidTy,
                                                              m_intptrTy));

      m_kleeMkSymbolicFn = cast<Function> (M.getOrInsertFunction ("klee_make_symbolic",
                                                                  voidTy,
                                                                  i8PtrTy,
                                                                  m_intptrTy,
                                                                  i8PtrTy));

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

      if (!m_tli)
	m_tli = &getAnalysis<TargetLibraryInfoWrapperPass> ().getTLI();

      // -- known library function
      LibFunc F;
      if (m_tli->getLibFunc (GV.getName(), F)) return false;

      if (m_externalNames.count (GV.getName()) > 0 ) return false;

      return true;
    }

    void defineFunction (Function &F)
    {
      LOG ("verbose", errs () << "Defining: " << F.getName () << "\n";);
      BasicBlock *bb = BasicBlock::Create (F.getContext(), "entry", &F);
      IRBuilder<> Builder (bb);

      Type *retTy = F.getReturnType ();
      if (retTy->isVoidTy ())
        Builder.CreateRetVoid ();
      else
      {
        uint64_t storeSzInBits = m_dl->getTypeStoreSizeInBits(retTy);
        Type* storeTy = retTy;

        // extend if store size is bigger than type size (mostly for i1)
        if (storeSzInBits > m_dl->getTypeSizeInBits (retTy))
          storeTy = Type::getIntNTy(F.getContext(),storeSzInBits);

        AllocaInst *v = Builder.CreateAlloca (storeTy);
        ConstantInt *sz = Builder.getIntN (m_intptrTy->getBitWidth(),
                                           storeSzInBits  / 8);
        GlobalVariable *fname = Builder.CreateGlobalString (F.getName ());

	// TODO: update callgraph with this call
        CallInst *mksym =
          Builder.CreateCall (m_kleeMkSymbolicFn,
			      {Builder.CreateBitCast (v, Builder.getInt8PtrTy ()),
			       sz,
			       Builder.CreateConstGEP2_32
				  (cast<PointerType>(fname->getType())->getElementType(),
				   fname, 0, 0)});

        Value *retValue = Builder.CreateLoad (v);
        if (storeTy != retTy)
          retValue = Builder.CreateZExtOrTrunc(retValue, retTy);

        Builder.CreateRet (retValue);
      }
    }

    void internalizeVariables (Module& M)
    {
       for (Module::global_iterator I = M.global_begin(), E = M.global_end();
          I != E; ++I) {
        GlobalVariable *GV = &*I;
        if (m_externalNames.count (GV->getName())) continue;
        // We previously tested for isConstant here, but extern arrays
        // are considered constant.
        if (GV->hasInitializer())
          continue;
        GV->setInitializer(Constant::getNullValue(GV->getType()->getElementType()));
        LOG ("verbose", errs() << "making " << GV->getName() << " non-extern\n";);
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

      m_externalNames.insert ("__VERIFIER_assume");
      m_externalNames.insert ("__VERIFIER_error");

      m_externalNames.insert ("__seahorn_get_value_i8");
      m_externalNames.insert ("__seahorn_get_value_i16");
      m_externalNames.insert ("__seahorn_get_value_i32");
      m_externalNames.insert ("__seahorn_get_value_i64");
      m_externalNames.insert ("__seahorn_get_value_ptr");

      m_externalNames.insert ("__seahorn_mem_store");
      m_externalNames.insert ("__seahorn_mem_load");
      m_externalNames.insert ("__seahorn_mem_init");
      m_externalNames.insert ("__seahorn_mem_alloc");      

      // -- LLVM stuff
      m_externalNames.insert("llvm.used");
      m_externalNames.insert("llvm.compiler.used");
      m_externalNames.insert("llvm.global_ctors");
      m_externalNames.insert("llvm.global_dtors");
      m_externalNames.insert("llvm.global.annotations");
      m_externalNames.insert("__stack_chk_fail");
      m_externalNames.insert("__stack_chk_guard");


      // -- libc
      m_externalNames.insert("__stdoutp");
      m_externalNames.insert("__stderrp");
      m_externalNames.insert("__stdinp");

    }

    void getAnalysisUsage (AnalysisUsage &AU) const override
    {
      AU.addRequired<TargetLibraryInfoWrapperPass> ();
      AU.setPreservesAll ();
    }

    bool runOnModule (Module &M)
    {
      declareKleeFunctions(M);
      internalizeVariables(M);

      for (Function &F : M)
      {
        if (shouldInternalize (F)) defineFunction (F);
        else if (!F.isDeclaration()) runOnFunction (F);
      }
      return true;
    }


    bool runOnFunction (Function &F)
    {
      LOG("verbose", errs() << "Processing: " << F.getName () << "\n";);
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
            ninst = Builder.CreateCall (m_assertFailFn,
                                       {Builder.CreateGlobalStringPtr ("FAILED"),
					Builder.CreateGlobalStringPtr ("__builtin.c"),
                                        Builder.getInt32 (0),
					   Builder.CreateConstGEP2_32 (
					       cast<PointerType>(fname->getType()->getScalarType())->getElementType(), 
					       fname, 0, 0)});

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
