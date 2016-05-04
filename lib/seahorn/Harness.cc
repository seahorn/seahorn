#include "seahorn/Harness.hh"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/ValueMap.h"

#include "boost/algorithm/string/replace.hpp"

#include <memory>

using namespace llvm;
namespace seahorn
{

  Constant* exprToLlvm (Type *ty, Expr e)
  {
    if (isOpX<TRUE> (e))
      return Constant::getIntegerValue (ty, APInt(ty->getPrimitiveSizeInBits(), 1));
    else if (isOpX<FALSE> (e))
      return Constant::getNullValue (ty);
    else if (isOpX<MPZ> (e))
    {
      mpz_class mpz = getTerm<mpz_class> (e);
      if (ty->isIntegerTy ())
        return Constant::getIntegerValue (ty,
                                          APInt(ty->getPrimitiveSizeInBits(),
                                                mpz.get_str (), 10));
      else if (ty->isPointerTy()) {
        // XXX Need DataLayout to allocate properly sized integer
        // XXX For now, return NULL value
        return Constant::getNullValue (ty);
      }
    }
    else
    {
      // if all fails, try 0
      LOG("cex", errs () << "WARNING: Not handled value: " << *e << "\n";);
      return Constant::getNullValue (ty);
    }
    llvm_unreachable("Unhandled expression");
  }

  std::unique_ptr<Module>  createLLVMHarness(BmcTrace &trace)
  {

    std::unique_ptr<Module> Harness = make_unique<Module>("harness", getGlobalContext());

    ValueMap<const Function*, ExprVector> FuncValueMap;

    // Look for calls in the trace
    for (unsigned loc = 0; loc < trace.size(); loc++)
    {
      const BasicBlock &BB = *trace.bb(loc);
      for (auto &I : BB)
      {
        if (const CallInst *ci = dyn_cast<CallInst> (&I))
        {
          ImmutableCallSite CS(ci);
          const Function *CF = CS.getCalledFunction ();
          if (!CF) continue;

          errs () << "Looking at: " << CF->getName () << "\n";

          if (!CF->hasName()) continue;
          if (CF->getName().find_first_of('.') != StringRef::npos) continue;
          if (!CF->isExternalLinkage (CF->getLinkage ())) continue;
          if (!CF->getReturnType()->isIntegerTy () &&
              !CF->getReturnType()->isPointerTy())
            continue;

          Expr V = trace.eval (loc, I, true);
          if (!V) continue;
          FuncValueMap[CF].push_back(V);
        }
      }
    }

    // Build harness functions
    for (auto CFV : FuncValueMap) {

      auto CF = CFV.first;
      auto& values = CFV.second;

      // This is where we will build the harness function
      Function *HF =
        cast<Function>
        (Harness->getOrInsertFunction(CF->getName(),
                                      cast<FunctionType>
                                      (CF->getFunctionType())));

      Type *RT = CF->getReturnType();
      Type *pRT = nullptr;
      if (RT->isIntegerTy ()) pRT = RT->getPointerTo ();
      else pRT = Type::getInt8PtrTy (getGlobalContext());
      
      
      ArrayType* AT = ArrayType::get(RT, values.size());

      // Convert Expr to LLVM constants
      SmallVector<Constant*, 20> LLVMarray;
      std::transform(values.begin(), values.end(), std::back_inserter(LLVMarray),
                     [RT](Expr e) { return exprToLlvm(RT, e); });

      // This is an array containing the values to be returned
      GlobalVariable* CA = new GlobalVariable(*Harness,
                                              AT,
                                              true,
                                              GlobalValue::PrivateLinkage,
                                              ConstantArray::get(AT, LLVMarray));
      
      // Build the body of the harness function
      BasicBlock *BB = BasicBlock::Create(getGlobalContext(), "entry", HF);
      IRBuilder<> Builder(BB);

      Type *CountType = Type::getInt32Ty (getGlobalContext());
      GlobalVariable* Counter = new GlobalVariable(*Harness,
                                                   CountType,
                                                   false,
                                                   GlobalValue::PrivateLinkage,
                                                   ConstantInt::get(CountType, 0));

      Value *LoadCounter = Builder.CreateLoad(Counter);
      //Value* Idx[] = {ConstantInt::get(CountType, 0), LoadCounter};
      //Value *ArrayLookup = Builder.CreateLoad(Builder.CreateInBoundsGEP(CA, Idx));

      Value* Args[] = {LoadCounter,
                       Builder.CreateBitCast(CA, pRT),
                       ConstantInt::get(CountType, values.size())};
      Type* ArgTypes[] = {CountType, pRT, CountType};

      Builder.CreateStore(Builder.CreateAdd(LoadCounter,
                                            ConstantInt::get(CountType, 1)),
                          Counter);

      std::string name;
      if (RT->isIntegerTy ())
      {
        std::string RS;
        llvm::raw_string_ostream RSO(RS);
        RT->print(RSO);
        
        name = Twine("__seahorn_get_value_").concat(RSO.str()).str();
      }
      else
        name = "__seahorn_get_value_ptr";
      
      Constant *GetValue =
        Harness->getOrInsertFunction(name,
                                     FunctionType::get(RT, makeArrayRef (ArgTypes, 3), 
                                                       false));
      assert(GetValue);
      Value* RetValue = Builder.CreateCall(GetValue, makeArrayRef(Args, 3));

      Builder.CreateRet(RetValue);
    }

    return (Harness);
  }
}
