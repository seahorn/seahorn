/** Unhoist expressions inside loops */

#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Analysis/ValueTracking.h"

#include "llvm/ADT/DenseSet.h"
#include "llvm/ADT/SmallVector.h"

#include "boost/range.hpp"

using namespace llvm;

namespace seahorn
{
  template <typename F>
  void replaceAllUsesIn (Value &Old, Value &New, F &filter);

  class LoopUnhoist : public FunctionPass
  {
  private:
    bool isMovable (const Value &v)
    {
      if (const Instruction *inst = dyn_cast<const Instruction> (&v))
        return isMovable (*inst);
      return false;
    }
    
    /// return true if the instruction can be safely moved inside a loop
    bool isMovable (const Instruction &inst)
    {
      const Instruction *op = &inst;
      if (isa<PHINode> (op)) return false;
      
      if (op->mayHaveSideEffects () ||
          op->mayReadOrWriteMemory ()) return false;
      if (isa<DbgInfoIntrinsic> (op)) return false;
      if (isa<LandingPadInst> (op)) return false;
      if (isa<AllocaInst> (op)) return false;
      
      return isSafeToSpeculativelyExecute (op);
    }
    
    
  public:
    static char ID;
    
    LoopUnhoist () : FunctionPass (ID) {}
    
    virtual void getAnalysisUsage (AnalysisUsage &AU) const override
    {
      AU.setPreservesAll ();
      AU.addRequiredTransitive<LoopInfoWrapperPass> ();
    }
    
    virtual bool runOnFunction (Function &F) override
    {
      bool Changed = false;
      
      errs () << "Looking at: " << F.getName () << "\n";
      
      LoopInfo &li = getAnalysis<LoopInfoWrapperPass>().getLoopInfo();
      
      // instructions to unhoist
      SmallVector<Instruction*, 16> todo;
      // maps old to new
      DenseMap<Instruction*, Instruction*> map;
      
      for (Loop *loop : li)
      {
        todo.clear ();
        map.clear ();
        
        // -- skip loops that do not have a header
        if (!loop->getHeader ()) continue;
        
        for (BasicBlock *bb : loop->getBlocks ())
          for (auto &inst : *bb)
            for (Value *v : boost::make_iterator_range (inst.value_op_begin (),
                                                        inst.value_op_end ()))
              if (Instruction *op = dyn_cast<Instruction> (v))
              {
                // already processed
                if (map.count (op)) continue;
                
                if (!loop->isLoopInvariant (op) || !isMovable (*op)) continue;
                todo.push_back (op);
                map [op] = op->clone ();
              }
      
        Changed = !todo.empty ();
        
        // replace all uses inside the loop by new expressions
        for (auto &kv : map) replaceAllUsesIn (*kv.first, *kv.second, *loop);
        
        
        // -- clone new code into loop header
	BasicBlock::iterator insertPt = loop->getHeader ()->getFirstInsertionPt ();
        while (!todo.empty ())
        {
          Instruction *clone = map [todo.back ()];
          assert (clone);
          
          unsigned sz = todo.size ();
          
          for (Use &u : boost::make_iterator_range (clone->op_begin (),
                                                    clone->op_end ()))
          {
            if (isMovable (*u.get ()))
            {
              Instruction *inst = dyn_cast<Instruction> (u.get ());
              auto it = map.find (inst);
              if (it != map.end ()) u.set (it->second);
              else
              {
                todo.push_back (inst);
                map [inst] = inst->clone ();
              }
            }
          }
          if (sz > todo.size ()) continue;
          
          if (todo.back ()->hasName ())
            clone->setName (todo.back ()->getName ());
          
          todo.pop_back ();
	  clone->insertBefore (&*insertPt);
          errs () << "Unhoisting: " << *clone << "\n";
        }
      }
      
      return Changed;
    }
    
    
    
    
  };
  
  char LoopUnhoist::ID = 0;
  
  /// Replaces all uses of Old with New in the BasicBlocks in the set
  template <typename F>
  void replaceAllUsesIn (Value &Old, Value &New, F &filter)
  {
    SmallVector<Use*, 16> uses;
    for (auto it = Old.use_begin (), end = Old.use_end (); it != end; ++it)
    {
      Use &U = *it;
      
      if (Constant *C = dyn_cast<Constant> (U.getUser ()))
        if (!isa<GlobalValue> (C)) continue;
      
      if (Instruction *inst = dyn_cast<Instruction> (U.getUser ()))
        if (filter.contains (inst->getParent ())) uses.push_back (&U);
    }
  
    // -- set all uses
    for (Use *u : uses) u->set (&New);
  }
}

static llvm::RegisterPass<seahorn::LoopUnhoist>
X ("unhoist", "Unhoist expressions inside loops");


