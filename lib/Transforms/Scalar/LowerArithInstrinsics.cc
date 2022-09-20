#include "llvm/ADT/Statistic.h"
#include "llvm/Pass.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"

#include "boost/range.hpp"

#define DEBUG_TYPE "lower-arith-intrinsics"

STATISTIC(NumLoweredArithIntrinsics, 
          "Number of arithmetic with overflow intrinsics lowered");

using namespace llvm;

namespace 
{
  class LowerArithIntrinsics : public FunctionPass
  {
  public:
    static char ID;
    
    LowerArithIntrinsics () : FunctionPass (ID) {} 

    bool replaceArithIntrinsics (BinaryOperator::BinaryOps Op, CallInst* I, 
                                 const Twine& Name, LLVMContext& ctx){
      bool changed = false;
      SmallVector<ExtractValueInst*, 16> uses;
      bool canbe_lowered = true;
      for (Use &U : I->uses ()) {
        if (ExtractValueInst* EV = dyn_cast<ExtractValueInst> (U.getUser())) {
          if (EV->getNumIndices () == 1) {
            uses.push_back (EV);
            continue;
          }
        }
        canbe_lowered = false;
      }
      
      if (canbe_lowered) 
      {
        changed = true;
        Value *nv = BinaryOperator::Create(Op, I->getOperand(0), I->getOperand(1),
                                           Name, I);
        
        for (auto EV: uses) 
        {
          assert (EV->getNumIndices () == 1);
          if (EV->getIndices()[0] == 0) {
            EV->replaceAllUsesWith (nv);
          } else {
            EV->replaceAllUsesWith (ConstantInt::getFalse (ctx));
          }
        }
        NumLoweredArithIntrinsics++;
      }
      return changed;
    }

    bool runOnFunction (Function &F) override
    {
      if (F.empty ()) return false;
      
      bool changed = false;

      LLVMContext& ctx = F.getContext ();
      for (auto &I : instructions(F))
      {
        if (!isa<CallInst> (&I)) continue;

        CallInst &CI = cast<CallInst>(I);
        
        const Function *fn = CI.getCalledFunction ();
        if (!fn && CI.getCalledOperand())
          fn = dyn_cast<const Function> (CI.getCalledOperand()->stripPointerCasts ());

        if (!fn) continue;

        if ((fn->getName ().startswith ("llvm.sadd.with.overflow") ||
             fn->getName ().startswith ("llvm.uadd.with.overflow"))) {
          replaceArithIntrinsics (Instruction::Add, dyn_cast<CallInst> (&I), "", ctx);
        } else if ((fn->getName ().startswith ("llvm.ssub.with.overflow") ||
                    fn->getName ().startswith ("llvm.usub.with.overflow"))) {
          replaceArithIntrinsics (Instruction::Sub, dyn_cast<CallInst> (&I), "", ctx);
        } else if ((fn->getName ().startswith ("llvm.smul.with.overflow") ||
                    fn->getName ().startswith ("llvm.umul.with.overflow"))) {
          replaceArithIntrinsics (Instruction::Mul, dyn_cast<CallInst> (&I), "", ctx);
        }
      }
      
      return changed;
    }

    void getAnalysisUsage (AnalysisUsage &AU) const override
    {AU.setPreservesAll ();}
    
    virtual StringRef getPassName () const override 
    {return "Lower Arithmetic with Overflow Intrinsics";}
    
  };

  char LowerArithIntrinsics::ID = 0;
}

namespace seahorn
{
  Pass *createLowerArithWithOverflowIntrinsicsPass () 
  {return new LowerArithIntrinsics ();} 
}

static llvm::RegisterPass<LowerArithIntrinsics> 
X ("lower-arith-overflow-intrinsics", "Lower arithmetic with overflow intrinsics");
