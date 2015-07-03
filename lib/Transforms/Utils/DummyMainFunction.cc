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


#include "boost/range.hpp"

#include "seahorn/Transforms/Utils/DummyMainFunction.hh"

using namespace llvm;

static llvm::cl::opt<std::string>
EntryPoint("entry-point",
             llvm::cl::desc ("Entry point if main does not exist"),
             llvm::cl::init ("main"));

namespace seahorn
{

  char DummyMainFunction::ID = 0;
 
  bool DummyMainFunction::runOnModule (Module &M)
  {
    if (m_main == "") m_main = EntryPoint;
      
    Function *Main = M.getFunction ("main");
    if (Main) return false;
   
    Function *oldMain = M.getFunction (m_main.c_str ());   
    if (!oldMain) return false;
   
    LLVMContext &ctx = M.getContext ();
   
    ArrayRef <Type*> params;
    FunctionType *newMainTy = FunctionType::get (Type::getInt32Ty (ctx), 
						 params, 
						 false);
                      
    Function *newMain = Function::Create (newMainTy,
					  oldMain->getLinkage (),
					  "main", 
					  &M);

    newMain->copyAttributesFrom (oldMain);

    oldMain->setLinkage (GlobalValue::LinkageTypes::PrivateLinkage);

    BasicBlock *entry = BasicBlock::Create (ctx, "entry", newMain);
                                            			    
    IRBuilder<> Builder (ctx);
    Builder.SetInsertPoint (entry, entry->begin ());

    SmallVector<Value*,16> fargs;
    for (auto &a : boost::make_iterator_range (oldMain->arg_begin (), 
                                               oldMain->arg_end ()))
    {    
      // -- We can have for now an undef value because seapp we
      // -- will run later on createNonInitPass to turn undef into
      // -- nondet.
      fargs.push_back (UndefValue::get (a.getType ()));
    }


    CallInst *mcall = Builder.CreateCall (oldMain, fargs);

    if (oldMain->getReturnType () == Type::getInt32Ty (ctx))
       Builder.CreateRet ( mcall);
    else
       Builder.CreateRet ( ConstantInt::get (newMain->getReturnType (), 42));

    return true;
  }
} // end namespace   
      
static llvm::RegisterPass<seahorn::DummyMainFunction>
X ("dummy-main", 
   "Dummy main function", 
   false, false);
   
