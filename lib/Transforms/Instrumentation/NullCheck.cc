/*
 * Instrument a program to add null dereference checks
 */

#include "seahorn/Transforms/Instrumentation/NullCheck.hh"

#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Constants.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"

// For proving absence of null dereferences this option better be
// enabled. However, for finding code inconsistencies it might be
// useful to disable it.
static llvm::cl::opt<bool>
OptimizeNullChecks("null-check-optimize",
                   llvm::cl::desc ("Minimize the number of instrumented null checks"),
                   llvm::cl::init (false));

namespace seahorn
{
  using namespace llvm;

  Value* getBasePtr (Value *V, SmallPtrSet<Instruction *, 8> &SeenInsts) {

    V = V->stripPointerCasts();
    if (Instruction *I = dyn_cast<Instruction>(V)) {
      // If we have already seen this instruction, bail
      // out. Cycles can happen in unreachable code after constant
      // propagation.
      if (!SeenInsts.insert(I).second)
        return nullptr;

      if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(V)) {
        if (GEP->isInBounds() && GEP->getPointerAddressSpace() == 0) {
          // if the pointer is the base of some gep that is directly
          // read from memory we give up.
          if (isa<LoadInst>(GEP->getPointerOperand()))
            return GEP->getPointerOperand();
          else
            return getBasePtr(GEP->getPointerOperand(), SeenInsts);
        } else
          return nullptr;
      }
      if (LoadInst *LI = dyn_cast<LoadInst>(V))
        return getBasePtr(LI->getPointerOperand(), SeenInsts);
      if (StoreInst *SI = dyn_cast<StoreInst>(V))
        return getBasePtr(SI->getPointerOperand(), SeenInsts);

      return nullptr;
    }
    if (Argument *A = dyn_cast<Argument>(V))
      return V;
    if (isa<ConstantPointerNull>(V) || isa<UndefValue>(V))
      return V;
    if (isa<GlobalAlias>(V) || isa<GlobalVariable>(V))
      return V;
    if (ConstantExpr *CE = dyn_cast<ConstantExpr>(V)) {
      if (CE->getOpcode() == Instruction::GetElementPtr)
        return getBasePtr(cast<GEPOperator>(*CE).getPointerOperand(), SeenInsts);
    }
    return nullptr;
  }

  Value* getBasePtr (Value *V) {
    SmallPtrSet<Instruction *, 8> SeenInsts;
    return getBasePtr(V, SeenInsts);
  }

  void NullCheck::insertNullCheck (Value *Ptr, IRBuilder<> B, Instruction* I) {
    B.SetInsertPoint (I);
    Value* isNull = B.CreateIsNull (Ptr);
    isNull->setName ("null_check");

    if (Constant* C = dyn_cast<Constant> (isNull)) {
      if (ConstantInt* CI = dyn_cast<ConstantInt> (C)) {
        if (CI == ConstantInt::getFalse (B.getContext ())) {
          LOG ("null-check", errs () << "Memory access is trivially safe " << *I <<"\n";);
          TrivialChecks++;
        }
        else if (CI == ConstantInt::getTrue (B.getContext ())) {
          LOG ("null-check", errs () << "Memory access is trivially unsafe " << *I << "\n";);
          TrivialChecks++;
        }
      }
    }


    // Attach debug information to the new instruction
    if (Instruction* isNullI = dyn_cast<Instruction> (isNull)) {
      isNullI->setDebugLoc (I->getDebugLoc ());
      LOG ("null-check",
           errs () << "Added check for "
                   << I->getParent()->getParent()->getName() << "::"
                   << *(Ptr->stripPointerCasts()) << "\n";
           );
      ChecksAdded++;
    }

    TerminatorInst* ThenTerm = nullptr;
    TerminatorInst* ElseTerm = nullptr;

    SplitBlockAndInsertIfThenElse(isNull, I, &ThenTerm, &ElseTerm);

    assert (ThenTerm);

    // ThenTerm is always a BranchInst so this cast should never fail
    BranchInst *BI = cast<BranchInst> (ThenTerm);

    BasicBlock* ErrorBB = createErrorBlock (*I->getParent ()->getParent (), B);
    BI->setSuccessor(0, ErrorBB);
  }

  BasicBlock* NullCheck::createErrorBlock (Function &F, IRBuilder<> B) {

    BasicBlock* errBB = BasicBlock::Create(B.getContext (), "NullError", &F);
    B.SetInsertPoint (errBB);
    CallInst * CI = B.CreateCall (ErrorFn);
    B.CreateUnreachable ();

    // update call graph
    if (CG) {
      auto f1 = CG->getOrInsertFunction (&F);
      auto f2 = CG->getOrInsertFunction (ErrorFn);
      f1->addCalledFunction (CallSite (CI), f2);
    }

    return errBB;
  }

  bool NullCheck::runOnFunction (Function &F)
  {
    if (F.isDeclaration ()) return false;

    SmallSet<Value*, 16> TempsToInstrument;
    std::vector<Instruction*> Worklist;
    for (auto&BB : F)  {
      TempsToInstrument.clear();
      for (auto &i: BB) {
        Instruction *I = &i;
        if (isa<LoadInst>(I)) {

	  if (OptimizeNullChecks) {
	    if (Value* BasePtr = getBasePtr (I)) {
	      // We've checked BasePtr in the current BB.
	      if (!TempsToInstrument.insert(BasePtr).second) {
		LOG ("null-check",
		     errs () << "Skipped " << *BasePtr << " because already checked!\n";);
		continue;
	      }
	    }
	  }

          Worklist.push_back (I);
        } else if (isa<StoreInst>(I)) {

	  if (OptimizeNullChecks) {
	    if (Value* BasePtr = getBasePtr (I)) {
	      // We've checked BasePtr in the current BB.
	      if (!TempsToInstrument.insert(BasePtr).second) {
		LOG ("null-check",
		     errs () << "Skipped " << *BasePtr << " because already checked!\n";);
		continue;
	      }
	    }
          }

          Worklist.push_back (I);
        }
	else {
	  // TODO memory intrinsics
	}
      }
    }

    LLVMContext &ctx = F.getContext ();
    IRBuilder<> B (ctx);

    bool change = false;
    for (auto I: Worklist) {

      Value *Ptr = nullptr;
      if (auto *LI = dyn_cast<LoadInst>(I)) {
        Ptr = LI->getPointerOperand();
      } else if (auto *SI = dyn_cast<StoreInst>(I)) {
        Ptr = SI->getPointerOperand();
      } else {
	errs () << "ERROR: unknown instruction " << *I << "\n";
	continue;
      }
      assert (Ptr);

      Value * Base = nullptr;
      if (OptimizeNullChecks) Base = getBasePtr(Ptr);

      // -- Instrument the memory access
      insertNullCheck (Base ? Base : Ptr, B, I);

      if (!OptimizeNullChecks) {
	// -- Add extra memory safety assumption: successful load/store
	//    implies validity of their arguments.
	if (GetElementPtrInst* gep = dyn_cast<GetElementPtrInst>(Ptr)) {
	  if (gep->isInBounds() && gep->getPointerAddressSpace() == 0) {
	    Value* base = gep->getPointerOperand ();
	    B.SetInsertPoint (I);
	    auto It = B.GetInsertPoint();
	    ++It;
	    B.SetInsertPoint(I->getParent(), It);
	    CallInst* CI = B.CreateCall(AssumeFn, B.CreateIsNotNull(base));
	    CI->setDebugLoc (I->getDebugLoc ());

	    LOG ("null-check",
		 errs () << "Added memory safety assumption for " << *base << "\n";);

	    // update call graph
	    if (CG) {
	      auto f1 = CG->getOrInsertFunction (&F);
	      auto f2 = CG->getOrInsertFunction (AssumeFn);
	      f1->addCalledFunction (CallSite (CI), f2);
	    }
	  }
	}
      }
      change = true;
    }
    return change;
  }

  bool NullCheck::runOnModule (llvm::Module &M) {

    if (M.begin () == M.end ()) return false;

    // Get call graph
    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    if (cgwp) CG = &cgwp->getCallGraph ();

    LLVMContext &ctx = M.getContext ();

    AttrBuilder B;
    AttributeList as = AttributeList::get (ctx,
					   AttributeList::FunctionIndex,
					   B);

    AssumeFn = dyn_cast<Function>
        (M.getOrInsertFunction ("verifier.assume",
                                as,
                                Type::getVoidTy (ctx),
                                Type::getInt1Ty (ctx)));

    B.addAttribute (Attribute::NoReturn);
    B.addAttribute (Attribute::ReadNone);
    ErrorFn = dyn_cast<Function> (M.getOrInsertFunction ("verifier.error",
                                                         as,
                                                         Type::getVoidTy (ctx)));
    bool change = false;
    for (Function &F : M) {
      if (F.isDeclaration ()) continue;
      change |= runOnFunction (F);
    }

    errs () << "-- Inserted " << ChecksAdded << " null dereference checks "
            << " (skipped " << TrivialChecks << " trivial checks).\n";

    return change;
  }

  void NullCheck::getAnalysisUsage (llvm::AnalysisUsage &AU) const {
    AU.setPreservesAll ();
    AU.addRequired<CallGraphWrapperPass> ();
    AU.addPreserved<CallGraphWrapperPass> ();
  }

  char NullCheck::ID = 0;

    Pass* createNullCheckPass(){return new NullCheck();}

} // end namespace seahorn
static llvm::RegisterPass<seahorn::NullCheck>
X ("null-check", "Insert null dereference checks", false, false);
