#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"

#include "llvm/ADT/Statistic.h"
#include "llvm/Target/TargetLibraryInfo.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/ScalarEvolution.h"
#include "llvm/Analysis/ScalarEvolutionExpander.h"
#include "llvm/Analysis/ScalarEvolutionExpressions.h"

#include "llvm/Support/raw_ostream.h"

#include "boost/range.hpp"
#include "avy/AvyDebug.h"

using namespace llvm;

#define DEBUG_TYPE "simplify-pointer-loops"

STATISTIC(LoopsTransformed, "Number of pointer loops transformed");

namespace 
{
  /* 
     Simplify loops with pointer induction variables.
   */
  class SimplifyPointerLoops : public FunctionPass
  {
   public:

    static char ID;

   private:

    /// Data Layout.
    const TargetLibraryInfo* m_tli;
    /// Target Library Info.
    const DataLayout* m_dl;
    /// Scev analysis to use.
    ScalarEvolution *m_se;

    struct InductionInfo {
      Value* m_start;
      uint64_t m_step;
      int64_t m_stride;
      
      InductionInfo (): 
          m_start (nullptr), m_step (0), m_stride (0) { }
      InductionInfo (uint64_t step, int64_t stride): 
          m_start (nullptr), m_step (step), m_stride (stride) { }
      InductionInfo (Value* start, uint64_t step, int64_t stride): 
          m_start (start), m_step (step), m_stride (stride) { }
    };

    typedef DenseMap <PHINode*, InductionInfo> InductionMapTy;
    /* 
      Integer loops often have one integer induction
      variables. However, c++ iterators have often multiple pointer
      induction variables so we get all.
    */
    InductionMapTy m_inductions;
    
    bool hasOutsideLoopUser (const Loop *TheLoop, Instruction *Inst){
      //Check that all of the users of the loop are inside the BB.
      for (User *U : Inst->users()) {
        Instruction *UI = cast<Instruction>(U);
        // This user may be a reduction exit value.
        if (!TheLoop->contains(UI)) {
          LOG ("ptr-iv", errs () 
               << "Found an outside user for : " 
               << *UI << '\n');
          return true;
        }
      }
      return false;
    }

    bool isPointerInductionVariable (PHINode *Phi) {
      Type *PhiTy = Phi->getType();

      // We only handle pointer induction variables.
      if (!PhiTy->isPointerTy())
        return false;

      Type *PointerElementType = PhiTy->getPointerElementType();
      // The pointer stride cannot be determined if the pointer
      // element type is not sized.
      if (!PointerElementType->isSized())
        return false;

      // Check that the PHI is a recurrence.
      const SCEV *PhiScev = m_se->getSCEV(Phi);
      const SCEVAddRecExpr *AR = dyn_cast<SCEVAddRecExpr>(PhiScev);
      if (!AR) {
        LOG ("ptr-iv", errs () << "PHI is not a poly recurrence.\n");
        return false;
      }

      // Calculate the pointer stride and check if it is consecutive.
      const SCEV *Step = AR->getStepRecurrence(*m_se);
      const SCEVConstant *C = dyn_cast<SCEVConstant>(Step);
      if (!C)
        return false;

      // Calculate strided access
      uint64_t Size = m_dl->getTypeAllocSize(PointerElementType);
      const APInt &APStepVal = C->getValue()->getValue();
      int64_t StepVal = APStepVal.getSExtValue();
      int64_t Stride = StepVal / Size;
      int64_t Rem = StepVal % Size;
      if (Rem)
        return false;

      if (C->getValue()->equalsInt(Size)) {
        m_inductions [Phi] = InductionInfo (Size, Stride);
        return true;
      } else if (C->getValue()->equalsInt(0 - Size)) {
        LOG ("ptr-iv", errs () << "Reverse pointer induction not supported");
      }
      
      return false;
    }

   
    bool getPointerInductionVariables (Loop* TheLoop) {

      BasicBlock *PreHeader = TheLoop->getLoopPreheader();
      if (!PreHeader)
        return false;

      BasicBlock *Header = TheLoop->getHeader();
      if (!Header)
        return false;

      // For each block in the loop.
      for (Loop::block_iterator bb = TheLoop->block_begin(),
               be = TheLoop->block_end(); bb != be; ++bb) {
        // Scan the instructions in the block and look for hazards.
        for (BasicBlock::iterator it = (*bb)->begin(), e = (*bb)->end(); it != e;
             ++it) {
          
          if (PHINode *Phi = dyn_cast<PHINode>(it)) {
            Type *PhiTy = Phi->getType();
            // Check that this PHI type is a pointer
            if (!PhiTy->isPointerTy ()) {
              LOG("ptr-iv", errs () << "Found a non-pointer PHI node\n");
              return false;
            }

            // XXX: not sure if this restriction is needed
            if (*bb != Header) {
              if (!hasOutsideLoopUser(TheLoop, it))
                continue;
              return false;
            }
            
            // We only allow if-converted PHIs with exactly two incoming values.
            if (Phi->getNumIncomingValues() != 2) {
              LOG ("ptr-iv", errs () << "Found a PHI != two incoming blocks\n");
              return false;
            }
            
            // This is the value coming from the preheader.
            Value *StartValue = Phi->getIncomingValueForBlock(PreHeader);
            // Check if this is an induction variable.
            if (isPointerInductionVariable(Phi)) {
              // XXX: not sure if this restriction is needed
              if (hasOutsideLoopUser(TheLoop, it))
                return false;
              InductionInfo& II = m_inductions [Phi];
              II.m_start = StartValue;

              LOG ("ptr-iv", 
                   errs () << "Found IV " << *Phi 
                   << " with step " << II.m_step
                   << " and start=" << *(II.m_start) << "\n");
            }
          }
        }
      }
      return true;
    }

    BranchInst* getLoopExitBr (Loop* TheLoop) {
      if (BasicBlock* Exit = TheLoop->getExitingBlock ()) {
        TerminatorInst* TI = Exit->getTerminator ();
        if (BranchInst* BI = dyn_cast<BranchInst> (TI)) {
          if (BI->isConditional ())
            return BI;
        }
      }
      return nullptr;
    }

    CmpInst* getLoopExitCond (Loop* TheLoop) {
      BranchInst* BI  = getLoopExitBr (TheLoop);
      if (BI && BI->isConditional ()) {
        return dyn_cast<CmpInst> (BI->getCondition ());
      }
      return nullptr;
    }


    /* 
       Transform 
          p = start;
          do { p'=p+step; } while (p' != q);
       into
          p = start;
          do { p'=p+step; } while (p'+step <= q);
    */
    bool convertDisEqToIneqWithSlack (Loop* TheLoop, IRBuilder<> B) {
      // This transformation makes the assumption that p' does not go
      // beyond to q. This assumption may not hold.

      BasicBlock* ExitBB = TheLoop->getExitBlock ();
      if (!ExitBB) {
          // LOG ("simplify-pointer-loops" , 
          //      errs () << "Failed because multiple exit blocks\n");
          return false;
      }

      CmpInst* ExitCond = getLoopExitCond (TheLoop);
      if (!ExitCond) {
          // LOG ("simplify-pointer-loops" , 
          //      errs () << "Failed because exit condition not found\n");
          return false;
      }

      if (ExitCond->getPredicate () != CmpInst::ICMP_EQ && 
          ExitCond->getPredicate () != CmpInst::ICMP_NE) {
          // LOG ("simplify-pointer-loops" , 
          //      errs () << "Failed because loop exit condition is not a disequality\n");
          return false;
      }

      BasicBlock* TrueDest = nullptr;
      BasicBlock* FalseDest = nullptr;
      BranchInst* BI = getLoopExitBr (TheLoop);     
      if (BI && BI->isConditional ()) {
        TrueDest =  BI->getSuccessor (0);
        FalseDest = BI->getSuccessor (1);
      } else {
        // LOG ("simplify-pointer-loops" , 
        //      errs () << "Failed because unconditional loop exit\n");
        return false;
      }
      

      Value* Op1 = ExitCond->getOperand(0);
      Value* Op2 = ExitCond->getOperand(1);

      GetElementPtrInst* Gep1 = dyn_cast<GetElementPtrInst>(Op1);
      GetElementPtrInst* Gep2 = dyn_cast<GetElementPtrInst>(Op2);

      if (!Gep1 && !Gep2) {
        LOG ("simplify-pointer-loops" , 
             errs () << "Failed because no GEP operand found in loop exit condition." 
             << *Op1 << "\n"
             << *Op2 << "\n");
        return false;
      }
      
      PHINode* Phi1 = (!Gep1 ? nullptr : dyn_cast<PHINode> (Gep1->getPointerOperand ()));
      PHINode* Phi2 = (!Gep2 ? nullptr : dyn_cast<PHINode> (Gep2->getPointerOperand ()));
      
      if (!Phi1 && !Phi2) {
        LOG ("simplify-pointer-loops" , 
             errs () << "Failed because no GEP base operand is a PHI node.";
             if (Gep1) errs () << *Gep1 << "\n";
             if (Gep2) errs () << *Gep2 << "\n";);
        return false;
      }

      Value* LoopIndexGep = nullptr;
      Value* End = nullptr;
      InductionInfo II;      
      bool IV_found = false;
      if (Phi1) {
        auto It = m_inductions.find (Phi1);
        if (It != m_inductions.end ()) {
          II = It->second;
          LoopIndexGep = Gep1;
          End = Op2;
          IV_found = true;
        }
      }
      if (!IV_found && Phi2) {
        auto It = m_inductions.find (Phi2);
        if (It != m_inductions.end ()) {
          II = It->second;
          LoopIndexGep = Gep2;
          End = Op1;
          IV_found = true;
        }
      }

      if (!IV_found)  {
        LOG ("simplify-pointer-loops" , 
             errs () << "Failed because not IV found in loop exit condition";
             if (Phi1) errs () << *Phi1 << "\n";
             if (Phi2) errs () << *Phi2 << "\n";);
        return false;
      }
 
      assert (LoopIndexGep);
      assert (End);
      
      B.SetInsertPoint (ExitCond);
      Type *intPtrTy = m_dl->getIntPtrType (B.getContext(), 0);
      Value* Stride = ConstantInt::get (intPtrTy, II.m_stride);
      Value* Slack = B.CreateGEP (LoopIndexGep, Stride, "slack");

      Value * NExitCond = nullptr;
      if (TrueDest == ExitBB && ExitCond->getPredicate () == CmpInst::ICMP_EQ) {
        /* 
           %c = icmp eq %loopIndexGep %end
           br %c %exit %loop        
        */
        NExitCond = B.CreateICmpSGT(Slack, End);
      } else if (FalseDest == ExitBB && ExitCond->getPredicate () == CmpInst::ICMP_NE) {
        /* 
           %c = icmp neq %loopIndexGep %end
           br %c %loop %exit
        */
        NExitCond = B.CreateICmpSLE(Slack, End);
      } else {
        // Slack was already inserted
        return true;
      }
      
      ExitCond->replaceAllUsesWith (NExitCond);

      LOG ("simplify-pointer-loops",
           errs () << "Replaced " << *ExitCond << " with " << *NExitCond << "\n");

      LoopsTransformed++;
      return true;
    }

   public:

    SimplifyPointerLoops () : FunctionPass (ID) {} 

    bool runOnFunction (Function &F)
    {
      if (F.empty ()) return false;

      m_tli = &getAnalysis<TargetLibraryInfo>();
      m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
      m_se = &getAnalysis<ScalarEvolution>();      
      LoopInfo* LI = &getAnalysis<LoopInfo>();      

      for (auto L : boost::make_iterator_range (LI->begin (), LI->end ())) {
        getPointerInductionVariables (L);
      }

      IRBuilder<> B (F.getContext ());
      bool Change = false;
      for (auto L : boost::make_iterator_range (LI->begin (), LI->end ())) {
        Change |= convertDisEqToIneqWithSlack (L, B);
      }
      return Change;
    }

    void getAnalysisUsage (AnalysisUsage &AU) const {
      AU.setPreservesAll ();
      AU.addRequired<LoopInfo>();
      AU.addRequired<ScalarEvolution> ();
      AU.addRequired<TargetLibraryInfo> ();
      AU.addRequired<DataLayoutPass> ();
    }
    
    virtual const char *getPassName () const 
    {return "Simplify Loops with Pointer Induction Variables";}
    
  };

  char SimplifyPointerLoops::ID = 0;
}

namespace seahorn
{
  Pass *createSimplifyPointerLoopsPass () 
  {return new SimplifyPointerLoops ();} 
}

static llvm::RegisterPass<SimplifyPointerLoops> 
X ("simplify-pointer-loops", 
   "Simplify loops with pointer induction variables");
