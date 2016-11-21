#include "seahorn/Transforms/Scalar/LowerGvInitializers.hh"

#include "boost/range.hpp"
#include "boost/format.hpp"

#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/IRBuilder.h"

#include "avy/AvyDebug.h"

namespace seahorn
{
  char LowerGvInitializers::ID = 0;


  /// XXX: from CtorUtils.cpp
  /// 
  /// Given a llvm.global_ctors list that we can understand,
  /// return a list of the functions and null terminator as a vector.
  std::vector<Function *> parseGlobalCtors(GlobalVariable *GV) {
    if (GV->getInitializer()->isNullValue())
      return std::vector<Function *>();
    ConstantArray *CA = cast<ConstantArray>(GV->getInitializer());
    std::vector<Function *> Result;
    Result.reserve(CA->getNumOperands());
    for (User::op_iterator i = CA->op_begin(), e = CA->op_end(); i != e; ++i) {
      ConstantStruct *CS = cast<ConstantStruct>(*i);
      Result.push_back(dyn_cast<Function>(CS->getOperand(1)));
    }
    return Result;
  }


  /// XXX: from CtorUtils.cpp
  /// 
  /// Find the llvm.global_ctors list, verifying that all initializers have an
  /// init priority of 65535.
  GlobalVariable *findGlobalCtors(Module &M) {
    
    GlobalVariable *GV = M.getGlobalVariable("llvm.global_ctors");
    if (!GV)
      return nullptr;
    
    // Verify that the initializer is simple enough for us to handle. We are
    // only allowed to optimize the initializer if it is unique.
    if (!GV->hasUniqueInitializer())
      return nullptr;
    
    if (isa<ConstantAggregateZero>(GV->getInitializer()))
      return GV;
    ConstantArray *CA = cast<ConstantArray>(GV->getInitializer());
    
    for (User::op_iterator i = CA->op_begin(), e = CA->op_end(); i != e; ++i) {
      if (isa<ConstantAggregateZero>(*i))
	continue;
      ConstantStruct *CS = cast<ConstantStruct>(*i);
      if (isa<ConstantPointerNull>(CS->getOperand(1)))
	continue;
      
      // Must have a function or null ptr.
      if (!isa<Function>(CS->getOperand(1)))
	return nullptr;
      
      // Init priority must be standard.
      ConstantInt *CI = cast<ConstantInt>(CS->getOperand(0));
      if (CI->getZExtValue() != 65535)
	return nullptr;
    }
    return GV;
  }


      
  //XXX: From DummyMainFunction.cpp
  Function& makeNewNondetFn (Module &m, Type &type, unsigned num, std::string prefix) {
    std::string name;
    unsigned c = num;
    do
      name = boost::str (boost::format (prefix + "%d") % (c++));
    while (m.getNamedValue (name));
    Function *res = dyn_cast<Function>(m.getOrInsertFunction (name, &type, NULL));
    assert (res);
    return *res;
  }
    
  Constant* LowerGvInitializers::getNondetFn (Type *type, Module& M) {
    Constant* res = m_ndfn [type];
    if (!res) {
      res = &makeNewNondetFn (M, *type, m_ndfn.size (), "verifier.nondet.");
      m_ndfn[type] = res;
    }
    return res;
  }
  
  // Add instructions in main that initialize global variables.
  bool LowerGvInitializers::runOnModule (Module &M) {

    const DataLayout* DL = &getAnalysis<DataLayoutPass>().getDataLayout ();

    Function *f = M.getFunction ("main");
    if (!f) {
      LOG ("lower-gv-init",
	   errs () << "LowerGvInitializers: there is no main so nothing to lower\n");     
      return false;
    }
    
    IRBuilder<> Builder (f->getContext ());
    
    Builder.SetInsertPoint (&f->getEntryBlock (), f->getEntryBlock ().begin ());

    bool change=false;
    
    // Iterate over global variables
    for (GlobalVariable &gv : boost::make_iterator_range (M.global_begin (),
                                                          M.global_end ()))
    {
      if (!gv.hasInitializer ()) continue;
      PointerType *ty = dyn_cast<PointerType> (gv.getType ());
      if (!ty) continue;
      Type *ety = ty->getElementType ();
      // only deal with scalars for now
      if (ety->isIntegerTy () || ety->isPointerTy ())
      {
      
        // -- create a store instruction
        StoreInst* SI= Builder.CreateAlignedStore (gv.getInitializer (), &gv, 
						   DL->getABITypeAlignment (ety));

        LOG ("lower-gv-init",
             errs () << "LowerGvInitializers: created a store " << *SI << "\n");
	
        change=true;
      }
      else
	errs () << "WARNING: Ignoring initializer for" << gv << "\n";
    }

    // Iterate over global constructors
    if (GlobalVariable * GlobalCtors = findGlobalCtors (M)) {
      auto CtorFns = parseGlobalCtors (GlobalCtors);
      if (!CtorFns.empty ())
	change = true;
	
      for (auto Fn : CtorFns) {
        // -- create a call with non-deterministic parameters
        SmallVector<Value*, 16> Args;
        for (auto &A : Fn->args ()) {
          Constant *ndf = getNondetFn (A.getType (), M);
          Args.push_back (Builder.CreateCall (ndf));
        }
        CallInst* CI = Builder.CreateCall (Fn, Args);
        LOG ("lower-gv-init",
             errs () << "LowerGvInitializers: created a call " << *CI << "\n");
      }
    }    
      
    return change;
  }

}

static llvm::RegisterPass<seahorn::LowerGvInitializers>
X ("lower-gv-init", "Lower initialization of global variables");
