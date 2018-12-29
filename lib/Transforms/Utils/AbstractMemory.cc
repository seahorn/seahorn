#include "llvm/Pass.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/LoopInfo.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/ADT/SmallVector.h"

#include "boost/range.hpp"
#include "boost/format.hpp"
#include "boost/unordered_set.hpp"

#include "seahorn/Support/SeaDebug.h"


/***
   This pass abstracts memory instructions.

   The abstractions are meant only for memory safety properties. All
   the abstractions are sound but they are simply heuristics. The two
   major abstractions are:

   1) The lhs of a load instruction is replaced with a
      non-deterministic value if two conditions hold:

      a) lhs cannot feed a memory instruction operand directly or indirectly.
      b) lhs is not used in a loop condition.

   2) The value operand of a store instruction is replaced with a
      non-deterministic value unless we believe the size of an
      allocation function is being stored.

   XXX: we have also implemented other abstractions (e.g., abstract
   the pointer operand of a load or store) but they are not currently
   exposed.
****/

using namespace llvm;

namespace seahorn
{
  enum MemAbsLevel {
    ONLY_LOAD,
    ONLY_STORE,
    LOAD_AND_STORE
  };
}
 
static llvm::cl::opt<enum seahorn::MemAbsLevel>
MAL("abstract-memory-level",
   llvm::cl::desc ("Track level for memory abstraction"),
    cl::values (clEnumValN (seahorn::ONLY_LOAD,
			    "only-load", "Only load instructions"),
		clEnumValN (seahorn::ONLY_STORE,
			    "only-store", "Only store instructions"),
		clEnumValN (seahorn::LOAD_AND_STORE,
			    "load-and-store", "Both load and store instructions")),
   cl::init (seahorn::LOAD_AND_STORE));


namespace seahorn
{

  class AbstractMemory : public ModulePass
  {

  private:

    typedef boost::unordered_set<const Instruction*> InstSet;
    
    void updateCg(Function* caller, CallInst* callee) {
      if (m_cg) {
	ImmutableCallSite CS (callee);
	if (CS.getCalledFunction ()) {
	  m_cg->getOrInsertFunction (CS.getCalledFunction ());
	  (*m_cg)[caller]->addCalledFunction (CallSite (callee),
					      (*m_cg)[callee->getCalledFunction ()]);
	}
      }
    } 

    Function& makeNewNondetFn (Module &m, Type &type, unsigned num, std::string prefix)
    {
      std::string name;
      unsigned c = num;
      do
        name = boost::str (boost::format (prefix + "%d") % (c++));
      while (m.getNamedValue (name));
      Function *res = dyn_cast<Function>(m.getOrInsertFunction (name, &type));
      assert (res);
      return *res;
    }

    // create an external function "Type f(void)"
    Constant* getNondetFn (Type *type, Module& m, std::string prefix) {
      // XXX: at each call create a new function name.
      Constant* res = &makeNewNondetFn (m, *type, m_ndfn.size(),
					"verifier.nondet." + prefix);
      m_ndfn.push_back(res);
      return res;
    }


    Function& makeNewExternalFn (Module &m, Type &type, unsigned num, std::string prefix)
    {
      std::string name;
      unsigned c = num;
      do
        name = boost::str (boost::format (prefix + "%d") % (c++));
      while (m.getNamedValue (name));
      Function *res = dyn_cast<Function>(m.getOrInsertFunction
					 (name, Type::getVoidTy (m.getContext()),
					  &type));
      assert (res);
      return *res;
    }

    // create an external function "void f(Type)"    
    Constant* getExternalFn (Type *type, Module& m, std::string prefix) {
      Constant* res = m_extfn [type];
      if (!res) {
	res = &makeNewExternalFn (m, *type, m_extfn.size (),
				  "verifier.external." + prefix);
				  
	m_extfn[type] = res;
      }
      return res;
    }

    Instruction* getLoopExitCond (BasicBlock* ExitingLoop) {
      TerminatorInst* TI = ExitingLoop->getTerminator ();
      if (BranchInst* BI = dyn_cast<BranchInst> (TI)) {
        if (BI->isConditional ()) {
          return dyn_cast<Instruction> (BI->getCondition ());
        }
      }
      return nullptr;
    }

    // Loop conditions can be formed from multiple simpler conditions
    // combined via logical operators (and, or, xor).  We try here to
    // extract some of these simpler conditions.
    void breakComplexLoopConditions (Instruction *I, InstSet &S) {
      if (I->getOpcode () >= BinaryOperator::And &&
          I->getOpcode () <= BinaryOperator::Xor) {
        if (Instruction* I1 = dyn_cast <Instruction> (I->getOperand(0)))
          breakComplexLoopConditions (I1, S);
        if (Instruction* I2 = dyn_cast <Instruction> (I->getOperand(1)))
	  breakComplexLoopConditions (I2, S);	  
        return ;
      } else if (CmpInst*CI = dyn_cast <CmpInst> (I)) {
	S.insert (CI);
      }
    }

    void extractLoopConditions (Loop *TheLoop, InstSet &LoopConds) {
      SmallVector<BasicBlock*, 16> ExitingBlocks;
      TheLoop->getExitingBlocks (ExitingBlocks);
      for (BasicBlock* ExitingBlock : ExitingBlocks) {
        if (Instruction* ExitCond = getLoopExitCond (ExitingBlock))
	  breakComplexLoopConditions (ExitCond, LoopConds);
      }
    }
    
    // Return true if v may be used (directly or indirectly) as an
    // operand of a memory instruction or loop condition
    bool usedInMemoryInstOrLoopCond (const Value &v,
				     const InstSet &LoopConds,
				     boost::unordered_set<const Value*> &seen) {
      
      if (!seen.insert (&v).second) return false;

      for(auto const&U: v.uses())
      {
    	 if (const CallInst *CI = dyn_cast<const CallInst>(U.getUser()))
	 {
    	   ImmutableCallSite CS (CI);
    	   if (CS.getCalledFunction ()) 
    	     return true; // XXX: we give up if inter-procedural
    	 }
	  
    	 if (isa<const ReturnInst>(U.getUser()))
    	   return true;  // XXX: we give up if it escapes the function

    	 if (isa<const PHINode>(U.getUser()))
    	   return true;  // XXX: we give up with PHI nodes
	 
    	 if (const Instruction *I = dyn_cast<const Instruction>(U.getUser()))
    	 {
    	   // XXX: memory instruction: alloca, load, store, gep, fence, atomic*
    	   if (I->getOpcode () >= Instruction::Alloca &&
    	       I->getOpcode () <= Instruction::AtomicRMW)
    	     return true;

    	   // XXX: the instruction is used as loop condition
    	   if (LoopConds.count (I) > 0)
    	     return true;
    	 }

    	 if (usedInMemoryInstOrLoopCond (*(U.getUser()), LoopConds, seen))
    	   return true;
      }
      return false; 
    }

    // We abstract a load instruction unless its lhs is used directly
    // or indirectly by a memory instruction or loop condition
    bool shouldBeLoadAbstracted (LoadInst *I, const InstSet &LoopConds) {
      boost::unordered_set<const Value*> seen;
      return (!usedInMemoryInstOrLoopCond (*I, LoopConds, seen));
    }

    bool isSizeOfAllocationFn (Value &v) {
      if (!v.getType ()->isIntegerTy ()) return false;
      
      for(auto const&U: v.uses()) {
	if (isAllocationFn (U.getUser(), m_tli, true) || isa<AllocaInst> (U.getUser()))
	  return true;
	
	if (Instruction *I = dyn_cast<Instruction> (U.getUser())) {
	  // XXX: goes recursively if v may be used to compute the
	  // size of the allocated region.
	  if (I->isBinaryOp () || I->isCast ())
	    if (isSizeOfAllocationFn (*I))
	      return true;
	}
      }
      return false;
    }
    
    // We abstract a store instruction if v is a non-pointer which is
    // not used as a parameter to an allocation function.
    // 
    // v can be either getValOperand () or getPointerOperand ()
    bool shouldBeStoreAbstracted (Value &v) {
      if (v.getType ()->isPointerTy())
	return false;
      else if (isSizeOfAllocationFn (v))
	return false;      
      else
	return true;
    }

    Instruction* getInsPt (Value &v, Instruction &i) {
      
      // find the definition of v if exist
      Instruction * insPt = dyn_cast<Instruction> (&v);
      if (insPt && isa<PHINode>(insPt))
	insPt = insPt->getParent()->getFirstNonPHI();
      
      // if argument choose the first non-phi instruction in the entry
      // block of the function
      if (!insPt) 
      	if (isa<Argument> (&v)) {
	  Function &fn = *(i.getParent()->getParent());
      	  if (!fn.getEntryBlock().empty ())
      	    insPt = fn.getEntryBlock().getFirstNonPHI();
	}
	       
      LOG ("mem-abs",	
	   if (!insPt)
	   {
	     if (isa<Constant>(&v))
	       errs () << "Constant " << v << " ignored by memory abstraction\n";		 
	     else if (isa<GlobalVariable> (&v))
	       errs () << "Global  "  << v << " ignored by memory abstraction\n";
	     else
	       errs () << v << " ignored by memory abstraction\n";
	   });
      return insPt;
    }

    // Give a value v it creates a call "v' := nondet ()" where v' has
    // the same type than v.
    CallInst* mkNondetCall (Value &v, Module &m,
			    IRBuilder <> &B, Instruction * insPt,
			    std::string prefix) {
      Constant * fn = getNondetFn (v.getType (), m, prefix);
      B.SetInsertPoint (insPt);
      CallInst * ni = B.CreateCall (fn);
      updateCg (cast<Function>(fn), ni);
      ni->setDebugLoc (insPt->getDebugLoc ());
      return ni;
    }
    
    // Replace all uses of v with a non-deterministic value
    void replaceAllUsesWithNondet (Value &v, Module &m,
				   IRBuilder <> &B, Instruction * insPt,
				   std::string prefix) {
      CallInst *ni = mkNondetCall (v, m, B, insPt, prefix);
      v.replaceAllUsesWith (ni);
    }

    // Create a call to an external function that uses v
    void mkOneUse (Value &v, Instruction *I, Module &m, IRBuilder <> &B) {
      Constant* fn =getExternalFn (v.getType(), m, v.getName().str());
      // XXX: insert external call one instruction after I
      B.SetInsertPoint (I);	    
      auto insPt = B.GetInsertPoint ();
      insPt++;
      B.SetInsertPoint (&*insPt);
      Instruction * ni = B.CreateCall(fn, &v);
      updateCg (cast<Function>(fn), cast<CallInst> (ni));	  
      ni->setDebugLoc (I->getDebugLoc ());
    }

    // We can abstract a load instruction by :
    // (1) removing the load and replacing the lhs with a
    //     non-deterministic value, or
    // (2) abstracting the pointer operand 
    enum load_abs_lvl_t {
      LOAD_NONE = 0x0,
      LOAD_LHS  = 0x1,
      LOAD_PTR  = 0x2,
      LOAD_ALL  = 0x3
    };
    
    bool abstractLoad (LoadInst *I, IRBuilder <> &B,
		       const InstSet &LoopConds,
		       load_abs_lvl_t lvl = LOAD_LHS) {
      if (!shouldBeLoadAbstracted (I, LoopConds)) return false;

      Function &fn = *(I->getParent()->getParent());
      Module &m = *(fn.getParent());
      bool change = false;

      if (lvl & LOAD_LHS) {
	// x := *p  --> y := *p; x := nondet ();  (where y is a fresh variable)
	if (m_seen.insert (I).second) {
	  LOG ("mem-abs", errs () << "Replaced lhs of " << *I << " with a non-det value.\n");
	  Value &lhs = *I;
	  replaceAllUsesWithNondet (lhs, m, B, I, "abstract.memory.load.lhs.");
	  mkOneUse (lhs, I, m, B);
	  num_abs_load_deletions ++;
	  change = true;
	}
      }

      if (lvl & LOAD_PTR) {
	// x := *p  --> q := nondet_ptr (); x := *q;
	// Replaces all uses of p with q. This is probably too aggressive.
	// XXX: we might want to add assumptions deferenceable(q) and in-bound(q).	
	if (m_seen.insert (I->getPointerOperand ()).second) {      
	  if (Instruction *insPt = getInsPt (*(I->getPointerOperand ()), *I)) {
	    LOG ("mem-abs",
		 errs () << "Replaced pointer operand from " << *I
		         << " with a  non-deterministic value.\n");

	    replaceAllUsesWithNondet (*(I->getPointerOperand ()), m, B,
				      insPt, "abstract.memory.load.pointer.");	    
	    num_abs_load_pointers++;
	    change = true;
	  }
	}
      }
      
      return change;
    }

    // We can abstract a store instruction by 
    // -  abstracting the value operand (by replacing with non-deterministic value), or
    // -  abstracting the pointer operand (by replacing with non-deterministic value), or
    // -  deleting the instruction
    enum store_abs_lvl_t{
      // Delete Ptr  Val  
      //  0      0    0
      STORE_NONE = 0x0,
      // 0       0    1
      STORE_VAL = 0x1,
      // 0       1    0
      STORE_PTR = 0x2,
      // 0       1    1
      STORE_VAL_PTR = 0x3,
      // 1       0    0
      STORE_DEL = 0x4,
      // 1       0    1
      STORE_DEL_AND_VAL = 0x5,
      // 1       1    0
      STORE_DEL_AND_PTR = 0x6,      
      // 1       1    1
      STORE_ALL = 0x7      
    };
    
    bool abstractStore (StoreInst *I, IRBuilder <> &B, store_abs_lvl_t lvl = STORE_VAL) {
      Function &fn = *(I->getParent()->getParent());
      Module &m = *(fn.getParent());
      bool change = false;

      if (lvl & STORE_VAL) {
	// *p := v --> v' = nondet (); *p := v';
	Value &v = *(I->getValueOperand ());
	if (shouldBeStoreAbstracted (v) && m_seen.insert (&v).second) {
	  if (Instruction *insPt = getInsPt (v, *I)) {
	    LOG ("mem-abs",
		 errs () << "Replaced value operand from " << *I
		         << " with a non-deterministic value.\n");

	    //// XXX: replace all uses of v with v'. This might be too
	    //// aggressive.
	    // replaceAllUsesWithNondet (v, m, B, insPt,
	    // 			      "abstract.memory.store.value.");
	    // mkOneUse (v, I, m, B);

	    /////
	    // XXX: replace only the value operand of the store with
	    //      v' but other uses of v are not abstracted.
	    /////
	    CallInst *CI = mkNondetCall (v, m, B, insPt,
					 "abstract.memory.store.value.");
	    B.SetInsertPoint (I);
	    StoreInst *NI = B.CreateAlignedStore (CI, I->getPointerOperand (),
						  I->isVolatile (), I->getAlignment());
	    mkOneUse (v, I, m, B);	    
	    I->eraseFromParent ();
	    
	    num_abs_store_values++;
	    change = true;
	  }
	}
      }

      if (lvl & STORE_PTR) {
	// *p := v --> q := nondet (); *q :=v;
	// XXX: replace all uses of p with q. This might be too agressive. 
	// XXX: we might want to add assumptions deferenceable(q) and in-bound(q).
	Value &v = *(I->getPointerOperand ());	
	if (shouldBeStoreAbstracted (v) && m_seen.insert (&v).second) {      
	  if (Instruction *insPt = getInsPt (v, *I)) {
	    LOG ("mem-abs",
		 errs () << "Replaced pointer operand from " << *I
     		         << " with a non-deterministic vaue.\n");
	    
	    replaceAllUsesWithNondet (v, m, B, insPt,
				      "abstract.memory.store.pointer.");
	    num_abs_store_pointers++;
	    change = true;
	  }
	}
      }

      if (lvl & STORE_DEL && !(lvl & STORE_VAL)) {
	// XXX: if STORE_VAL bit is enabled then I has been deleted
	// and replaced with another store instruction
	// *p := v --> skip
	LOG ("mem-abs", errs () << "Deleted " << *I << "\n");
	
	I->eraseFromParent ();
	num_abs_store_deletions++;	
	change = true;
      }
      
      return change;
    }

    
   public:

    static char ID;

   private:

    TargetLibraryInfo *m_tli;
    CallGraph* m_cg;   
    std::vector<Constant*> m_ndfn;
    //DenseMap<const Type*, Constant*> m_ndfn;
    DenseMap<const Type*, Constant*> m_extfn;    
    boost::unordered_set <const Value*> m_seen;

    // --- counters for stats
    unsigned int num_abs_load_deletions;
    unsigned int num_abs_load_pointers;    
    unsigned int num_abs_store_values;
    unsigned int num_abs_store_pointers;
    unsigned int num_abs_store_deletions;        
    
   public:

    AbstractMemory () :
      ModulePass (ID), m_tli (nullptr), m_cg (nullptr),
      num_abs_load_deletions (0), num_abs_load_pointers (0),
      num_abs_store_values (0), num_abs_store_pointers (0),
      num_abs_store_deletions (0) {}

    bool runOnFunction (Function &F)
    {
      if (F.isDeclaration () || F.empty ()) return false;

      LoopInfo *li = &getAnalysis<LoopInfoWrapperPass>(F).getLoopInfo();
      InstSet LoopConds;
      for (Loop *L: boost::make_iterator_range (li->begin(), li->end ())) {
	extractLoopConditions (L, LoopConds);
      }
      
      std::vector<Instruction*> Worklist;
      for (auto &I : boost::make_iterator_range(inst_begin (F), inst_end (F)))
	if (isa<LoadInst> (&I) || isa<StoreInst> (&I))
	  Worklist.push_back (&I);

      if (Worklist.empty ()) return false;

      LLVMContext &ctx = F.getParent()->getContext ();
      IRBuilder<> B (ctx);
      
      bool Change = false;
      while (!Worklist.empty()) 
      {
	Instruction* I = Worklist.back();
	Worklist.pop_back();
	if (LoadInst * LI = dyn_cast<LoadInst>(I)) {
	  Change |= abstractLoad (LI, B, LoopConds,
				  (MAL == ONLY_STORE) ?
				  load_abs_lvl_t::LOAD_NONE :
				  load_abs_lvl_t::LOAD_LHS);
	} else if (StoreInst * SI = dyn_cast<StoreInst>(I))
	  Change |= abstractStore (SI, B,
				   (MAL == ONLY_LOAD) ?
				   store_abs_lvl_t::STORE_NONE :
				   store_abs_lvl_t::STORE_VAL);
      }      
      return Change;
    }
    
    bool runOnModule (Module &M)
    {      
      m_tli = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
      CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
      m_cg = cgwp ? &cgwp->getCallGraph () : nullptr;
                 
      bool Change = false;
      for (auto &F: M) Change |= runOnFunction (F);

      // errs () << "After AbstractMemory pass \n" << M << "\n";
      
      /// --- add non-deterministic functions to llvm.used
      GlobalVariable *LLVMUsed = M.getGlobalVariable("llvm.used");
      std::vector<Constant*> MergedVars;
      if (LLVMUsed) {
        // Collect the existing members of llvm.used
        ConstantArray *Inits = cast<ConstantArray>(LLVMUsed->getInitializer());
        for (unsigned I = 0, E = Inits->getNumOperands(); I != E; ++I) {
          Value* V = Inits->getOperand(I)->stripPointerCasts();
          MergedVars.push_back(Inits->getOperand(I));
        }
        LLVMUsed->eraseFromParent();
      }
      
      Type *i8PTy = Type::getInt8PtrTy(M.getContext());
      // for (auto &ndfn: m_ndfn) 
      // 	MergedVars.push_back (ConstantExpr::getBitCast(ndfn, i8PTy));
      for (auto &kv: m_extfn) 
      	MergedVars.push_back (ConstantExpr::getBitCast(kv.second, i8PTy));
      
      // Recreate llvm.used.
      ArrayType *ATy = ArrayType::get(i8PTy, MergedVars.size());
      LLVMUsed = new llvm::GlobalVariable(
          M, ATy, false, llvm::GlobalValue::AppendingLinkage,
          llvm::ConstantArray::get(ATy, MergedVars), "llvm.used");
      LLVMUsed->setSection("llvm.metadata");

      errs () << " ========== Memory Abstraction Pass ==========\n";
      errs () << "\t Replaced "  << num_abs_load_deletions
	      << " lhs of load instructions with nondet values\n";
      if (num_abs_load_pointers > 0)
	errs () << "\t Replaced " << num_abs_load_pointers
		<< " pointer operands of load instructions with nondet values\n";	
      errs () << "\t Replaced " << num_abs_store_values       
	      << " values of store instructions with nondet values\n";
      if (num_abs_store_pointers > 0)
	errs () << "\t Replaced " << num_abs_store_pointers       
		<< " pointer operands of store instructions with nondet values\n";
      if (num_abs_store_deletions > 0)
	errs () << "\t Deleted " << num_abs_store_deletions << " store instructions\n";
	      
	
      
      return Change;
    }
    
    void getAnalysisUsage (AnalysisUsage &AU) const
    {
      AU.setPreservesAll ();
      AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
      AU.addRequired<llvm::CallGraphWrapperPass>();
      AU.addRequired<LoopInfoWrapperPass>();      
    }
    
    virtual StringRef getPassName () const 
    {return "Abstract memory instructions";}
  };


  char AbstractMemory::ID = 0;

  Pass* createAbstractMemoryPass ()
  { return new AbstractMemory (); }

} // end namespace   
