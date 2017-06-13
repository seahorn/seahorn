//===-------- Resolve indirect calls using signature match ----------------===//
//
// This class is almost the same than Devirt in DSA but it does not
// use alias analysis to compute the possible targets of an indirect
// call. Instead, it simply selects those functions whose signatures
// match.
//
//===----------------------------------------------------------------------===//


#define DEBUG_TYPE "devirt-functions"


#include "llvm/IR/Constants.h"
#include "llvm/Transforms/IPO.h"
#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/DerivedTypes.h"
#include "llvm/IR/InstVisitor.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Support/Debug.h"
#include "llvm/ADT/Statistic.h"

#include "seahorn/Transforms/Utils/Local.hh"

#include "avy/AvyDebug.h"

using namespace llvm;

static llvm::cl::opt<bool>
AllowIndirectCalls ("allow-indirect-calls",
                    llvm::cl::desc ("Allow creation of indirect calls "
                                    "during devirtualization "
                                    "(required for soundness)"),
                    llvm::cl::init (false));
namespace
{

  static bool isIndirectCall (CallSite &CS)
  {
    Value *v = CS.getCalledValue ();
    if (!v) return false;
    
    v = v->stripPointerCasts ();
    return !isa<Function> (v);
  }
  
  //
  // Class: DevirtualizeFunctions
  //
  // Description:
  //  This transform pass will look for indirect function calls and transform
  //  them into a switch statement that selects one of several direct function
  //  calls to execute.
  //
  class DevirtualizeFunctions : 
    public ModulePass, public InstVisitor<DevirtualizeFunctions> 
  {

    typedef const llvm::PointerType *AliasSetId;
    typedef SmallVector<const Function *, 8> AliasSet;

    // Call graph of the program
    CallGraph * CG;    

    // Worklist of call sites to transform
    SmallVector<Instruction*, 32> m_worklist;

    /// map from alias-id to the corresponding alias set
    DenseMap<AliasSetId, AliasSet> m_aliasSets;
    
    /// maps alias set id to an existing bounce function
    DenseMap<AliasSetId, Function*> m_bounceMap;
    
    /// turn the indirect call-site into a direct one
    void mkDirectCall (CallSite CS);
    /// create a bounce function that calls functions directly
    Function* mkBounceFn (CallSite &CS);
    
    
    /// returns an AliasId of the called value
    /// requires that CS is an indirect call through a function pointer
    AliasSetId typeAliasId (CallSite &CS) const
    {
      assert (isIndirectCall (CS) && "Not an indirect call");
      PointerType *pTy = dyn_cast<PointerType> (CS.getCalledValue ()->getType ());
      assert (pTy && "Unexpected call not through a pointer");
      assert (isa<FunctionType> (pTy->getElementType ())
              && "The type of called value is not a pointer to a function");
      return pTy;
    }
    
    /// returns an id of an alias set to which this function belongs
    AliasSetId typeAliasId (const Function &F) const
    {return F.getFunctionType ()->getPointerTo ();}
    
   public:
    static char ID;
    DevirtualizeFunctions() : ModulePass(ID), CG (nullptr) {}
    
    virtual bool runOnModule(Module & M);
    
    virtual void getAnalysisUsage(AnalysisUsage &AU) const
    {
      AU.setPreservesAll ();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.addPreserved<CallGraphWrapperPass> ();
    }
    
    // -- VISITOR IMPLEMENTATION --
    
    void visitCallSite(CallSite &CS);
    
    void visitCallInst(CallInst &CI)
    {
      // we cannot take the address of an inline asm
      if (CI.isInlineAsm ()) return;
      
      CallSite CS(&CI);
      visitCallSite(CS);
    }
    void visitInvokeInst(InvokeInst &II)
    {
      CallSite CS(&II);
      visitCallSite(CS);
    }
  };

  // Pass ID variable
  char DevirtualizeFunctions::ID = 0;

  // Pass statistics
  STATISTIC(FuncAdded, "Number of bounce functions added");
  STATISTIC(CSConvert, "Number of call sites resolved");

  static inline PointerType * getVoidPtrType (LLVMContext & C)
  {
    Type * Int8Type  = IntegerType::getInt8Ty(C);
    return PointerType::getUnqual(Int8Type);
  }

  static inline Value *
  castTo (Value * V, Type * Ty, std::string Name, Instruction * InsertPt)
  {
    // Don't bother creating a cast if it's already the correct type.
    if (V->getType() == Ty) return V;
    
    // If it's a constant, just create a constant expression.
    if (Constant * C = dyn_cast<Constant>(V))
    {
      Constant * CE = ConstantExpr::getZExtOrBitCast (C, Ty);
      return CE;
    }
    
    // Otherwise, insert a cast instruction.
    return CastInst::CreateZExtOrBitCast (V, Ty, Name, InsertPt);
  }

  /**
   * Creates a bounce function that calls functions in an alias set directly
   */
  Function* DevirtualizeFunctions::mkBounceFn (CallSite &CS)
  {
    ++FuncAdded;

    AliasSetId id = typeAliasId (CS);
    {
      assert (isIndirectCall (CS) && "Not an indirect call");
      auto it = m_bounceMap.find (id);
      if (it != m_bounceMap.end ()) return it->second;
    }
    
    // -- no direct calls in this alias set, nothing to construct
    if (m_aliasSets.count (id) <= 0) return nullptr;
    
    AliasSet &Targets = m_aliasSets [id];
    

    LOG("devirt",
        errs () << "Building a bounce for call site:\n"
        << *CS.getInstruction () << " using:\n";
        for (auto &f : Targets)
          errs () << "\t" << f->getName () << "\n";);
        
    // Create a bounce function that has a function signature almost
    // identical to the function being called.  The only difference is
    // that it will have an additional pointer argument at the
    // beginning of its argument list that will be the function to
    // call.
    Value* ptr = CS.getCalledValue();
    SmallVector<Type*, 8> TP;
    TP.push_back (ptr->getType ());
    for (auto i = CS.arg_begin(), e = CS.arg_end (); i != e; ++i) 
      TP.push_back ((*i)->getType());
    
    FunctionType* NewTy = FunctionType::get (CS.getType(), TP, false);
    Module * M = CS.getInstruction()->getParent()->getParent()->getParent();
    assert (M);
    Function* F = Function::Create (NewTy,
                                    GlobalValue::InternalLinkage,
                                    "seahorn.bounce",
                                    M);
    
    // Set the names of the arguments.  Also, record the arguments in a vector
    // for subsequence access.
    F->arg_begin()->setName("funcPtr");
    SmallVector<Value*, 8> fargs;
    for(auto ai = ++F->arg_begin(), ae = F->arg_end(); ai != ae; ++ai)
    {
      fargs.push_back(&*ai);
      ai->setName("arg");
    }
          
    // Create an entry basic block for the function.  All it should do is perform
    // some cast instructions and branch to the first comparison basic block.
    BasicBlock* entryBB = BasicBlock::Create (M->getContext(), "entry", F);
    
    // For each function target, create a basic block that will call that
    // function directly.
    DenseMap<const Function*, BasicBlock*> targets;
    for (const Function *FL : Targets)
    {
      // Create the basic block for doing the direct call
      BasicBlock* BL = BasicBlock::Create (M->getContext(), FL->getName(), F);
      targets[FL] = BL;
      // Create the direct function call
      CallInst* directCall = CallInst::Create (const_cast<Function*>(FL),
                                               fargs, "", BL);
      // update call graph
      if (CG) {
        auto fl_cg = CG->getOrInsertFunction (const_cast<Function*> (FL));
        auto cf_cg = CG->getOrInsertFunction (directCall->getCalledFunction ());
        fl_cg->addCalledFunction (CallSite (directCall), cf_cg);
      }
      
      // Add the return instruction for the basic block
      if (CS.getType()->isVoidTy())
        ReturnInst::Create (M->getContext(), BL);
      else
        ReturnInst::Create (M->getContext(), directCall, BL);
    }
    
    // Create a default basic block having the original indirect call
    BasicBlock * defaultBB = BasicBlock::Create (M->getContext(),
                                                 "default",
                                                 F);

    if (CS.getType()->isVoidTy())
      ReturnInst::Create (M->getContext(), defaultBB);
    else
    {
      Value* defaultRet = nullptr;
      if (AllowIndirectCalls)
        defaultRet = CallInst::Create (&*(F->arg_begin()), fargs, "", defaultBB);
      else
      {
        Function &fn = seahorn::createNewNondetFn (*M, *CS.getType (),
                                                   1, "nondet.bounce.fptr.");
        defaultRet = CallInst::Create (&fn, "", defaultBB);
      }
      ReturnInst::Create (M->getContext(), defaultRet, defaultBB);
    }
                          
    // Setup the entry basic block.  For now, just have it call the default
    // basic block.  We'll change the basic block to which it branches later.
    BranchInst * InsertPt = BranchInst::Create (defaultBB, entryBB);
    
    // Create basic blocks which will test the value of the incoming function
    // pointer and branch to the appropriate basic block to call the function.
    Type * VoidPtrType = getVoidPtrType (M->getContext());
    Value * FArg = castTo (&*(F->arg_begin()), VoidPtrType, "", InsertPt);
    BasicBlock * tailBB = defaultBB;
    for (const Function *FL : Targets)
    {
      
      // Cast the function pointer to an integer.  This can go in the entry
      // block.
      Value * TargetInt = castTo (const_cast<Function*>(FL),
                                  VoidPtrType,
                                  "",
                                  InsertPt);
      
      // Create a new basic block that compares the function pointer to the
      // function target.  If the function pointer matches, we'll branch to the
      // basic block performing the direct call for that function; otherwise,
      // we'll branch to the next function call target.
      BasicBlock* TB = targets [FL];
      BasicBlock* newB = BasicBlock::Create (M->getContext(),
                                             "test." + FL->getName(),
                                             F);
      CmpInst * setcc = CmpInst::Create (Instruction::ICmp,
                                         CmpInst::ICMP_EQ,
                                         TargetInt,
                                         FArg,
                                         "sc",
                                         newB);
      BranchInst::Create (TB, tailBB, setcc, newB);
      
      // Make this newly created basic block the next block that will be reached
      // when the next comparison will need to be done.
      tailBB = newB;
    }
    
    // Make the entry basic block branch to the first comparison basic block.
    InsertPt->setSuccessor(0, tailBB);

    // -- log the newly created function
    m_bounceMap.insert (std::make_pair (id, F));
    
    // Return the newly created bounce function.
    return F;
  }


  void DevirtualizeFunctions::mkDirectCall (CallSite CS)
  {
    const Function *bounceFn = mkBounceFn (CS);
    // -- something failed
    LOG("devirt", if (!bounceFn)
                    errs () << "No bounce function for: "
                            << *CS.getInstruction () << "\n";);
    
    if (!bounceFn) return;
    
    // Replace the original call with a call to the bounce function.
    if (CallInst* CI = dyn_cast<CallInst>(CS.getInstruction()))
    {
      // The last operand in the op list is the callee
      SmallVector<Value*, 8> Params;
      Params.reserve (std::distance (CI->op_begin(), CI->op_end()));
      Params.push_back (*(CI->op_end () - 1));
      Params.insert (Params.end (), CI->op_begin(), (CI->op_end() - 1));
      std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
      CallInst* CN = CallInst::Create (const_cast<Function*>(bounceFn),
                                       Params,
                                       name,
                                       CI);

      LOG ("devirt",
           errs () << "Call to bounce function: \n" << *CN << "\n";);
                 
      // update call graph
      if (CG)
      {
        CG->getOrInsertFunction (const_cast<Function*> (bounceFn));
        (*CG)[CI->getParent ()->getParent ()]->addCalledFunction
          (CallSite (CN), (*CG)[CN->getCalledFunction ()]);
      }

      CN->setDebugLoc (CI->getDebugLoc ());
      CI->replaceAllUsesWith(CN);
      CI->eraseFromParent();
    }
    else if (InvokeInst* CI = dyn_cast<InvokeInst>(CS.getInstruction()))
    {
      SmallVector<Value*, 8> Params;
      Params.reserve (std::distance (CI->arg_operands().begin (),
                                     CI->arg_operands().end ()));
      // insert first the callee 
      Params.push_back (CI->getCalledValue ());
      Params.insert (Params.end (), 
                     CI->arg_operands().begin (), 
                     CI->arg_operands().end());

      std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
      InvokeInst* CN = InvokeInst::Create (const_cast<Function*>(bounceFn),
                                           CI->getNormalDest(),
                                           CI->getUnwindDest(),
                                           Params,
                                           name,
                                           CI);

      LOG ("devirt",
           errs () << "Call to bounce function: \n" << *CN << "\n";);
                 
      // update call graph
      if (CG)
      {
        CG->getOrInsertFunction (const_cast<Function*> (bounceFn));
        (*CG)[CI->getParent ()->getParent ()]->addCalledFunction
          (CallSite (CN), (*CG)[CN->getCalledFunction ()]);
      }

      CN->setDebugLoc (CI->getDebugLoc ());
      CI->replaceAllUsesWith(CN);
      CI->eraseFromParent();
    }

    ++CSConvert;
    return;
  }
  
  void DevirtualizeFunctions::visitCallSite (CallSite &CS)
  {
    // -- skip direct calls
    if (!isIndirectCall (CS)) return;
    
    // This is an indirect call site.  Put it in the worklist of call
    // sites to transforms.
    m_worklist.push_back (CS.getInstruction());
    return;
  }

  bool DevirtualizeFunctions::runOnModule (Module & M)
  {
    // -- Get the call graph
    CG = &(getAnalysis<CallGraphWrapperPass> ().getCallGraph ());

    // -- Create alias sets
    for (auto const &F: M)
    {
      // -- intrinsics are never called indirectly
      if (F.isIntrinsic ()) continue;
      
      // -- local functions whose address is not taken cannot be
      // -- resolved by a function pointer
      if (F.hasLocalLinkage () && !F.hasAddressTaken ()) continue;

      // -- skip calls to declarations, these are resolved implicitly
      // -- by calling through the function pointer argument in the
      // -- default case of bounce function
      if (F.isDeclaration ()) continue;
      
      // -- skip seahorn and verifier specific intrinsics
      if (F.getName().startswith ("seahorn.")) continue;
      if (F.getName().startswith ("verifier.")) continue;
      // -- assume entry point is never called indirectly
      if (F.getName ().equals ("main")) continue;

      // -- add F to its corresponding alias set
      m_aliasSets [typeAliasId (F)].push_back (&F);
    }

    // Visit all of the call instructions in this function and record those that
    // are indirect function calls.
    visit (M);
    
    // Now go through and transform all of the indirect calls that we found that
    // need transforming.
    bool Changed = !m_worklist.empty ();
    for (auto I : m_worklist) {
      CallSite CS (I);
      mkDirectCall (CS);
    }

    // Conservatively assume that we've changed one or more call sites.
    return Changed;
  }
  


} // end namespace

namespace seahorn
{
  Pass* createDevirtualizeFunctionsPass () {return new DevirtualizeFunctions ();}
}

// Pass registration
static  RegisterPass<DevirtualizeFunctions>
XX ("devirt-functions", "Devirtualize indirect function calls using only types");


