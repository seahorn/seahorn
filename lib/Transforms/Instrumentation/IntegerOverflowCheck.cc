/* 
 * Insert signed integer overflow/underflow checks.
 */


#include "seahorn/Transforms/Instrumentation/IntegerOverflowCheck.hh"

#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/ADT/APInt.h"

#include "avy/AvyDebug.h"

static llvm::cl::opt<bool>
HasErrorFunc("overflow-check-has-error-function",
             llvm::cl::desc ("Available verifier.error function to denote error."),
             llvm::cl::init (true));

namespace seahorn
{
  using namespace llvm;

  char IntegerOverflowCheck::ID = 0;

  std::pair<Value*,Value*> getBounds (LLVMContext &ctx, Type *ty)
  {
    IntegerType *ity = static_cast<IntegerType*> (ty);
    APInt lb = APInt::getSignedMinValue (ity->getBitWidth ());
    APInt ub = APInt::getSignedMaxValue (ity->getBitWidth ());
    return std::make_pair ( ConstantInt::get (ctx, lb),
                            ConstantInt::get (ctx, ub) );
  }

   bool IntegerOverflowCheck::insertIntegerCheck (Value *res, Type* ty,
                                                  IRBuilder<> B,
                                                  LLVMContext &ctx,
                                                  Instruction& inst)
   {
     assert (!inst.isTerminator ());
     BasicBlock::iterator it = &inst;
     it++;
     B.SetInsertPoint (it);    

     std::pair<Value*,Value*> bounds = getBounds (ctx, ty);
     
     BasicBlock *OldBB0 = inst.getParent ();
     BasicBlock *Cont0 = OldBB0->splitBasicBlock (B.GetInsertPoint ());
     OldBB0->getTerminator ()->eraseFromParent ();
     BranchInst::Create (Cont0, OldBB0);
     
     B.SetInsertPoint (Cont0->getFirstNonPHI ());    
     
     Value* Underflow = B.CreateICmpSGE (res, 
                                         bounds.first,
                                         "IOC_underflow");

     if (Instruction* UnderflowI = dyn_cast<Instruction> (Underflow)) {
       UnderflowI->setDebugLoc (inst.getDebugLoc ());     
     }

     BasicBlock *OldBB1 = Cont0;
     BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint ());
     OldBB1->getTerminator ()->eraseFromParent();
     BranchInst::Create (Cont1, ErrorBB, Underflow, OldBB1);
     
     B.SetInsertPoint (Cont1->getFirstNonPHI ());    
     
     Value* Overflow = B.CreateICmpSLE (res, 
                                        bounds.second,
                                        "IOC_overflow");

     if (Instruction* OverflowI = dyn_cast<Instruction> (Overflow)) {
       OverflowI->setDebugLoc (inst.getDebugLoc ());     
     }
     
     BasicBlock *OldBB2 = Cont1;
     BasicBlock *Cont2 = OldBB2->splitBasicBlock(B.GetInsertPoint ());
     OldBB2->getTerminator ()->eraseFromParent();
     BranchInst::Create (Cont2, ErrorBB, Overflow, OldBB2);
     
     ChecksAdded++;
     return true;

   }

   void IntegerOverflowCheck::addErrorAndSafeLocs (IRBuilder<>B, Function &F)  {
     
     LLVMContext &ctx = B.getContext ();
     
     if (ErrorFn)
     {
       ErrorBB = BasicBlock::Create(ctx, "ERROR", &F);
       B.SetInsertPoint (ErrorBB);    
       CallInst * CI = B.CreateCall (ErrorFn);
       B.CreateUnreachable ();
       // update call graph
       if (CG) {
         auto f1 = CG->getOrInsertFunction (&F);
         auto f2 = CG->getOrInsertFunction (ErrorFn);
         f1->addCalledFunction (CallSite (CI), f2);
       }
       return;
     } 
    
     // --- Here we assume that we cannot use verifier.error to
     //     denote error.  Then, the original return statement is replaced
     //     with a block with an infinite loop while a fresh block
     //     named ERROR returning an arbitrary value is created. All
     //     unsafe checks jump to ERROR.  The original program has
     //     been fully inlined and the only function is "main" which
     //     should return an integer.
     
     BasicBlock *retBB = nullptr;
     ReturnInst *retInst = nullptr;
     for (BasicBlock& bb : F)
     {
       TerminatorInst * inst = bb.getTerminator ();
       if (inst && (retInst = dyn_cast<ReturnInst> (inst))) 
       {
         retBB = &bb;
         break;
       }
     }
     
     if (!retInst)
     {     
       if (F.getReturnType ()->isIntegerTy ())
       {
         ErrorBB = BasicBlock::Create(ctx, "ERROR", &F);
         B.SetInsertPoint (ErrorBB);    
         B.CreateRet ( ConstantInt::get (F.getReturnType (), 42)); 
       }
       else
         assert (false && 
                 "Only instrument functions that return an integer");
     }
     else
     {
       Value * retVal = retInst->getReturnValue ();
       
       if (retVal && retVal->getType ()->isIntegerTy ())
       {
         ErrorBB = BasicBlock::Create(ctx, "ERROR", &F);
         B.SetInsertPoint (ErrorBB);    
         B.CreateRet ( ConstantInt::get (retVal->getType (), 42));
       }
       else 
       {
         assert ( false &&
                  "Only instrument functions that return an integer");
       }
       
       // replace original return with an infinite loop
       
       B.SetInsertPoint (retInst);    
       BasicBlock::iterator It = B.GetInsertPoint ();
       SafeBB = retBB->splitBasicBlock(It, "SAFE");
       BranchInst *loopInst = BranchInst::Create (SafeBB);
       ReplaceInstWithInst(retInst, loopInst);
     }      
   }

  bool IntegerOverflowCheck::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;

    LLVMContext &ctx = F.getContext ();
    IRBuilder<> B (ctx);
      
    addErrorAndSafeLocs (B,F);

    assert (ErrorBB);

    bool change = false;

    std::vector<Instruction*> WorkList;
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      Instruction *I = &*i;

      // we don't cover for now vector integer operations
      if (!I->getType()->isIntegerTy ())
        continue;

      if (isa<BinaryOperator> (I)) { 
        switch (I->getOpcode ()) {
          case BinaryOperator::Add:
          case BinaryOperator::Sub:
          case BinaryOperator::Mul:
          case BinaryOperator::Shl:  
          case BinaryOperator::SDiv: 
          case BinaryOperator::SRem: 
            // rare case but SRem can produce overflow if MININT and -1.
            WorkList.push_back (I);
          default: ;
        }          
      }
      else if (isa<TruncInst> (I)) 
        WorkList.push_back (I);
    }

    for (auto I : WorkList) {
      if (isa<BinaryOperator> (I)) {
        switch (I->getOpcode ()) {
          case BinaryOperator::Add:
          case BinaryOperator::Sub:
          case BinaryOperator::Mul:
          case BinaryOperator::Shl:  
          case BinaryOperator::SDiv: 
          case BinaryOperator::SRem: {
            change |= insertIntegerCheck (I, I->getType (), B, ctx, *I);
            break;
          }
          default: ;
        }          
      } else if (TruncInst * TI = dyn_cast<TruncInst> (I)) {
        change |= insertIntegerCheck (TI->getOperand (0), TI->getOperand (0)->getType (), B, ctx, *I);
      } 
    }
        
    return change;
  }

  bool IntegerOverflowCheck::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
      
    LLVMContext &ctx = M.getContext ();

    if (HasErrorFunc) {
      AttrBuilder B;
      B.addAttribute (Attribute::NoReturn);
      B.addAttribute (Attribute::ReadNone);
      
      AttributeSet as = AttributeSet::get (ctx, 
                                           AttributeSet::FunctionIndex,
                                           B);
      
      ErrorFn = dyn_cast<Function>
          (M.getOrInsertFunction ("verifier.error",
                                  as,
                                  Type::getVoidTy (ctx), NULL));
    }
    
    bool change = false;
    for (Function &F : M) {
      change |= runOnFunction (F); 
    }

    errs () << "-- Inserted " << ChecksAdded << " signed integer overflow checks.\n";
    return change;
  }
    
  void IntegerOverflowCheck::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  } 
} // end namespace

static llvm::RegisterPass<seahorn::IntegerOverflowCheck> 
X ("overflow-check", 
   "Insert integer underflow/overflow checks");
   

