#include "seahorn/CexHarness.hh"

#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/LLVMContext.h"
#include "llvm/IR/ValueMap.h"
#include "llvm/IR/DataLayout.h"

#include "boost/algorithm/string/replace.hpp"
#include <memory>

using namespace llvm;
namespace seahorn
{

  Constant* exprToLlvm (Type *ty, Expr e, const DataLayout &dl)
  {
    if (isOpX<TRUE> (e))
      return Constant::getIntegerValue (ty, APInt(dl.getTypeStoreSizeInBits(ty), 1));
    else if (isOpX<FALSE> (e))
      return Constant::getNullValue (ty);
    else if (isOpX<MPZ> (e) || bv::is_bvnum (e))
    {
      mpz_class mpz;
      mpz = isOpX<MPZ> (e) ? getTerm<mpz_class> (e) : getTerm<mpz_class> (e->arg (0));
      if (ty->isIntegerTy () || ty->isPointerTy())
      {
        // return Constant::getIntegerValue (ty,
        //                                   APInt(dl.getTypeStoreSizeInBits(ty),
        //                                         mpz.get_str (), 10));
        return Constant::getIntegerValue (ty,
                                          toAPInt (dl.getTypeStoreSizeInBits (ty), mpz));
      }
      llvm_unreachable("Unhandled type");
    }
    else
    {
      // if all fails, try 0
      LOG("cex", errs () << "WARNING: Not handled value: " << *e << "\n";);
      return Constant::getNullValue (ty);
    }
    llvm_unreachable("Unhandled expression");
  }

  std::unique_ptr<Module>  createCexHarness(BmcTrace &trace, const DataLayout &dl)
  {

    std::unique_ptr<Module> Harness = make_unique<Module>("harness", getGlobalContext());

    Harness->setDataLayout (&dl);
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
	  // Go through bitcasts
	  const Value *CV = CS.getCalledValue ();
          const Function *CF = dyn_cast<Function> (CV->stripPointerCasts ());
          if (!CF) {
	    LOG ("cex",
		 errs () << "Skipping harness for " << *ci
		         << " because callee cannot be resolved\n");
	    continue;
	  }

          LOG("cex",
	      errs () << "Considering harness for: " << CF->getName () << "\n";);

          if (!CF->hasName()) continue;
          if (CF->isIntrinsic ()) continue;
          // We want to ignore seahorn functions, but not nondet
          // functions created by strip-extern
          if (CF->getName().find_first_of('.') != StringRef::npos &&
              !CF->getName().startswith("verifier.nondet.stripextern")) continue;
          if (!CF->isExternalLinkage (CF->getLinkage ())) continue;
          if (!CF->getReturnType()->isIntegerTy () &&
              !CF->getReturnType()->isPointerTy()) {
            // LOG("cex",
            //     errs () << "Skipping harness for " << CF->getName ()
	    //             << " because it returns type: " << *CF->getReturnType()
	    //             << "\n";);
            continue;
          }

          // TODO: Port detection of well-known library functions from
          // KleeInternalize
          if (CF->getName().equals ("calloc")) continue;
          
          Expr V = trace.eval (loc, I, true);
          if (!V) continue;
          LOG("cex",
	      errs () << "Producing harness for " << CF->getName () << "\n";);
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
                     [RT, dl](Expr e) { return exprToLlvm(RT, e, dl); });

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

      Builder.CreateStore(Builder.CreateAdd(LoadCounter,
                                            ConstantInt::get(CountType, 1)),
                          Counter);

      std::string name;
      std::vector <Type *> ArgTypes =
        {CountType, pRT, CountType};
      std::vector <Value *> Args =
        {LoadCounter,
         Builder.CreateBitCast(CA, pRT),
         ConstantInt::get(CountType, values.size())};

      if (RT->isIntegerTy ())
      {
        std::string RS;
        llvm::raw_string_ostream RSO(RS);
        RT->print(RSO);

        name = Twine("__seahorn_get_value_").concat(RSO.str()).str();
      }
      else if (RT->getSequentialElementType ()) {
        name = "__seahorn_get_value_ptr";
        ArgTypes.push_back (Type::getInt32Ty (getGlobalContext ()));

        // If we can tell how big the return type is, tell the
        // callback function.  Otherwise pass zero.
        if (RT->getSequentialElementType ()->isSized ())
          Args.push_back (ConstantInt::get (Type::getInt32Ty (getGlobalContext ()),
                                            dl.getTypeStoreSizeInBits (RT->getSequentialElementType ())));
        else
          Args.push_back (ConstantInt::get (Type::getInt32Ty (getGlobalContext ()), 0));
      }
      else
        assert (false && "Unknown return type");

      Constant *GetValue =
        Harness->getOrInsertFunction(name,
                                     FunctionType::get(RT,
                                                       makeArrayRef(ArgTypes),
                                                       false));
      assert(GetValue);
      Value* RetValue = Builder.CreateCall(GetValue, makeArrayRef (Args));

      Builder.CreateRet(RetValue);
    }

    return (Harness);
  }
}
