/* 
 * Instrument a program to add signed integer overflow/underflow
 * checks.  
 */

#include "seahorn/Transforms/Instrumentation/IntegerOverflowCheck.hh"

#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"

#include "llvm/ADT/APInt.h"

#include <boost/optional.hpp>
#include "avy/AvyDebug.h"

static llvm::cl::opt<bool>
InlineChecks("ioc-inline-all",
             llvm::cl::desc ("Insert checks assuming all functions have been inlined."),
             llvm::cl::init (false));

namespace seahorn
{
  using namespace llvm;

  char IntegerOverflowCheck::ID = 0;

  std::pair<Value*,Value*> getBounds (LLVMContext &ctx, Type *ty)
  {
    IntegerType *ity = dyn_cast<IntegerType> (ty);
    assert (ty && "Value should be an integer");
    
    APInt lb = APInt::getSignedMinValue (ity->getBitWidth ());
    APInt ub = APInt::getSignedMaxValue (ity->getBitWidth ());

    return std::make_pair ( ConstantInt::get (ctx, lb),
                            ConstantInt::get (ctx, ub) );
  }

   bool IntegerOverflowCheck::instrumentVal (Value *res, Type* ty,
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
     
     Value* Cmp1 = B.CreateICmpSGE (res, 
                                    bounds.first,
                                    "IOC_underflow");
     
     BasicBlock *OldBB1 = Cont0;
     BasicBlock *Cont1 = OldBB1->splitBasicBlock(B.GetInsertPoint ());
     OldBB1->getTerminator ()->eraseFromParent();
     BranchInst::Create (Cont1, m_err_bb, Cmp1, OldBB1);
     
     B.SetInsertPoint (Cont1->getFirstNonPHI ());    
     
     Value* Cmp2 = B.CreateICmpSLE (res, 
                                    bounds.second,
                                    "IOC_overflow");
     
     BasicBlock *OldBB2 = Cont1;
     BasicBlock *Cont2 = OldBB2->splitBasicBlock(B.GetInsertPoint ());
     OldBB2->getTerminator ()->eraseFromParent();
     BranchInst::Create (Cont2, m_err_bb, Cmp2, OldBB2);
     
     ChecksAdded++;
     return true;

   }

   void IntegerOverflowCheck::instrumentErrAndSafeBlocks (IRBuilder<>B, 
                                                          Function &F)
   {
     
     LLVMContext &ctx = B.getContext ();
     
     if (!m_inline_all)
     {
       m_err_bb = BasicBlock::Create(ctx, "Error", &F);
       B.SetInsertPoint (m_err_bb);    
       B.CreateCall (m_errorFn);
       B.CreateUnreachable ();
       return;
     } 
    
     // The original return statement is replaced with a block with an
     // infinite loop while a fresh block named ERROR returning an
     // arbitrary value is created. All unsafe checks jump to ERROR.
     // The original program has been fully inlined and the only
     // function is "main" which should return an integer.
     
     BasicBlock * retBB = nullptr;
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
         m_err_bb = BasicBlock::Create(ctx, "Error", &F);
         B.SetInsertPoint (m_err_bb);    
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
         m_err_bb = BasicBlock::Create(ctx, "ERROR", &F);
         B.SetInsertPoint (m_err_bb);    
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
       m_safe_bb = retBB->splitBasicBlock(It, "SAFE");
       BranchInst *loopInst = BranchInst::Create(m_safe_bb);
      ReplaceInstWithInst(retInst, loopInst);
     }      
   }

  bool IntegerOverflowCheck::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;

    if (m_inline_all && !F.getName ().equals ("main"))
    {
      errs () << "Warning: " << F.getName () << " is not instrumented.\n";
      return false;
    }

    LLVMContext &ctx = F.getContext ();
    IRBuilder<> B (ctx);
      
    instrumentErrAndSafeBlocks (B,F);
    assert (m_err_bb);

    bool change = false;

    std::vector<Instruction*> WorkList;
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) 
    {
      Instruction *I = &*i;
      if (isa<BinaryOperator> (I))
      {
        switch (I->getOpcode ())
        {
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

    for (auto I : WorkList)
    {
      if (isa<BinaryOperator> (I))
      {
        switch (I->getOpcode ())
        {
          case BinaryOperator::Add:
          case BinaryOperator::Sub:
          case BinaryOperator::Mul:
          case BinaryOperator::Shl:  
          case BinaryOperator::SDiv: 
          case BinaryOperator::SRem: 
            {
              change |= instrumentVal (I, I->getType (),
                                       B, ctx, *I);
              break;
            }
          default: ;
        }          
      }
      else if (TruncInst * TI = dyn_cast<TruncInst> (I))
      {
        change |= instrumentVal (TI->getOperand (0), TI->getOperand (1)->getType (),
                                 B, ctx, *I);
      } 
    }
        
    return change;
  }

  bool IntegerOverflowCheck::runOnModule (llvm::Module &M)
  {
    if (M.begin () == M.end ()) return false;
      
    LLVMContext &ctx = M.getContext ();

    if (!m_inline_all) m_inline_all = InlineChecks;
  
    if (!m_inline_all)
    {
      AttrBuilder B;
      B.addAttribute (Attribute::NoReturn);
      B.addAttribute (Attribute::ReadNone);
      
      AttributeSet as = AttributeSet::get (ctx, 
                                           AttributeSet::FunctionIndex,
                                           B);
      
      m_errorFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.error",
                                as,
                                Type::getVoidTy (ctx), NULL));
    }

    bool change = false;

    for (Function &F : M) 
      change |= runOnFunction (F); 

    LOG( "ioc-verify", 
         errs () << "[IOA] checks added: " << ChecksAdded << "\n");

    return change;
  }
    
  void IntegerOverflowCheck::getAnalysisUsage (llvm::AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<llvm::UnifyFunctionExitNodes> ();
  } 


}

static llvm::RegisterPass<seahorn::IntegerOverflowCheck> 
X ("ioc", "Insert integer underflow/overflow checks");
   

