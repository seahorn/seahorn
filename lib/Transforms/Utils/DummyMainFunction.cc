/** Insert dummy main function if one does not exist */

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"

#include "boost/format.hpp"

#include "seahorn/Transforms/Utils/DummyMainFunction.hh"

using namespace llvm;

static llvm::cl::opt<std::string>
EntryPoint("entry-point",
      llvm::cl::desc ("Entry point if main does not exist"),
      llvm::cl::init (""));

namespace seahorn
{

  char DummyMainFunction::ID = 0;

  Function& DummyMainFunction::
  makeNewNondetFn (Module &m, Type &type, unsigned num, std::string prefix)
  {
    std::string name;
    unsigned c = num;
    do
      name = boost::str (boost::format (prefix + "%d") % (c++));
    while (m.getNamedValue (name));
    Function *res = dyn_cast<Function>(m.getOrInsertFunction (name, &type, NULL));
    assert (res);
    return *res;
  }

  Constant* DummyMainFunction::getNondetFn (Type *type, Module& M) {
    Constant* res = m_ndfn [type];
    if (!res) {
      res = &makeNewNondetFn (M, *type, m_ndfn.size (), "verifier.nondet.");
      m_ndfn[type] = res;
    }
    return res;
  }
 
  bool DummyMainFunction::runOnModule (Module &M)
  {
    if (EntryPoint == "" || M.getFunction ("main")) 
      return false;

    Function* F = M.getFunction (EntryPoint);
    if (!F)  {
      errs () << "DummyMainFunction: " << EntryPoint << " not found.\n";
      errs () << M << "\n";
      return false;
    }

    LLVMContext &ctx = M.getContext ();
    Type* intTy = Type::getInt32Ty (ctx);

    ArrayRef <Type*> params;
    Function *main = Function::Create (FunctionType::get (intTy, params, false), 
                                       GlobalValue::LinkageTypes::InternalLinkage, 
                                       "main", &M);
    //main->copyAttributesFrom (F);

    IRBuilder<> B (ctx);
    BasicBlock *BB = BasicBlock::Create (ctx, "", main);
    B.SetInsertPoint (BB, BB->begin ());
    SmallVector<Value*, 16> Args;
    for (auto &A : F->args ()) {
       Constant *ndf = getNondetFn (A.getType (), M);
       Args.push_back (B.CreateCall (ndf));
    }

    B.CreateCall (F, Args);
    // our favourite exit code
    B.CreateRet ( ConstantInt::get (intTy, 42));

    GlobalVariable *LLVMUsed = M.getGlobalVariable("llvm.used");
    std::vector<Constant*> MergedVars;
    if (LLVMUsed) {
      // Collect the existing members of llvm.used except sea
      // functions
      ConstantArray *Inits = cast<ConstantArray>(LLVMUsed->getInitializer());
      for (unsigned I = 0, E = Inits->getNumOperands(); I != E; ++I) {
        Value* V = Inits->getOperand(I)->stripPointerCasts();
        MergedVars.push_back(Inits->getOperand(I));
      }
      LLVMUsed->eraseFromParent();
    }

    Type *i8PTy = Type::getInt8PtrTy(ctx);
    // Add uses for our data
    MergedVars.push_back (ConstantExpr::getBitCast(cast<llvm::Constant>(F), i8PTy));
    // XXX: this shouldn't be necessary but for some reason DCE
    // deletes main
    MergedVars.push_back (ConstantExpr::getBitCast(cast<llvm::Constant>(main), i8PTy));

    // Recreate llvm.used.
    ArrayType *ATy = ArrayType::get(i8PTy, MergedVars.size());
    LLVMUsed = new llvm::GlobalVariable(
        M, ATy, false, llvm::GlobalValue::AppendingLinkage,
        llvm::ConstantArray::get(ATy, MergedVars), "llvm.used");
    LLVMUsed->setSection("llvm.metadata");

    return true;
  }

  void DummyMainFunction::getAnalysisUsage (AnalysisUsage &AU)
  { AU.setPreservesAll ();}

} // end namespace   
      
static llvm::RegisterPass<seahorn::DummyMainFunction>
X ("dummy-main", "Dummy main function", false, false); 
   
