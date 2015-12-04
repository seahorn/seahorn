//===-------- Resolve indirect calls using signature match ----------------===//
//
// This class is almost the same than Devirt in DSA but it does not
// use alias analysis to compute the possible targets of an indirect
// call. Instead, it simply selects those functions whose signatures
// match.
//
//                     The LLVM Compiler Infrastructure
//
// This file was developed by the LLVM research group and is distributed under
// the University of Illinois Open Source License. See LICENSE.TXT for details.
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

#include "avy/AvyDebug.h"

#include <iostream>
#include <algorithm>
#include <iterator>
#include <set>

using namespace llvm;

namespace seahorn {

  //
  // Class: DevirtualizeFunctions
  //
  // Description:
  //  This transform pass will look for indirect function calls and transform
  //  them into a switch statement that selects one of several direct function
  //  calls to execute.
  //
  class DevirtualizeFunctions : public ModulePass, public InstVisitor<DevirtualizeFunctions> {

    typedef std::set<const Function *> func_set_t;

    // Access to the target data analysis pass
    const DataLayout * TD;

    // Call graph of the program
    CallGraph * CG;    

    // Worklist of call sites to transform
    std::vector<Instruction *> Worklist;

    // Keep track of functions with same type
    DenseMap<const FunctionType*, std::vector<const Function *> > signatureMap;
    
    // A cache of indirect call targets that have been converted already
    DenseMap<const Function *, func_set_t> bounceCache;
    
    void makeDirectCall (CallSite & CS);
    Function* buildBounce (CallSite cs,std::vector<const Function*>& Targets);
    const Function* findInCache (const CallSite & CS, func_set_t& Targets);
    void findTargets (CallSite & CS, std::vector<const Function*>& Targets);
    
   public:
    static char ID;
    DevirtualizeFunctions() : ModulePass(ID), CG (nullptr) {}
    
    virtual bool runOnModule(Module & M);
    
    virtual void getAnalysisUsage(AnalysisUsage &AU) const {
      AU.setPreservesAll ();
      AU.addRequired<DataLayoutPass>();
      AU.addRequired<CallGraphWrapperPass> ();
      AU.addPreserved<CallGraphWrapperPass> ();
    }
    
    void visitCallSite(CallSite &CS);
    
    void visitCallInst(CallInst &CI) {
      // we cannot take the address of an inline asm
      if (CI.isInlineAsm ()) return;
      
      CallSite CS(&CI);
      visitCallSite(CS);
    }
    void visitInvokeInst(InvokeInst &II) {
      CallSite CS(&II);
      visitCallSite(CS);
    }
  };

  // Pass ID variable
  char DevirtualizeFunctions::ID = 0;

  // Pass statistics
  STATISTIC(FuncAdded, "Number of bounce functions added");
  STATISTIC(CSConvert, "Number of call sites resolved");

  static inline PointerType * getVoidPtrType (LLVMContext & C) {
    Type * Int8Type  = IntegerType::getInt8Ty(C);
    return PointerType::getUnqual(Int8Type);
  }

  static inline Value *
  castTo (Value * V, Type * Ty, std::string Name, Instruction * InsertPt) {
    // Don't bother creating a cast if it's already the correct type.
    if (V->getType() == Ty)
      return V;
    
    // If it's a constant, just create a constant expression.
    if (Constant * C = dyn_cast<Constant>(V)) {
      Constant * CE = ConstantExpr::getZExtOrBitCast (C, Ty);
      return CE;
    }
    
    // Otherwise, insert a cast instruction.
    return CastInst::CreateZExtOrBitCast (V, Ty, Name, InsertPt);
  }

  // Targets contains all functions whose type signature match with CS.
  // This is purely syntactic and no alias analysis is involved.
  void DevirtualizeFunctions::
  findTargets (CallSite & CS, std::vector<const Function*>& Targets) {

    Type* pointeeCSTy = nullptr;
    if (PointerType * PTy = dyn_cast<PointerType> 
        (CS.getCalledValue()->stripPointerCasts()->getType())) {
      pointeeCSTy  = PTy->getElementType ();
      // -- only resolve indirect calls without casting
      if (PTy != CS.getCalledValue ()->getType ()) return;
      
      LOG("devirt",
          errs () << "CS is: " << *CS.getInstruction () << "\n"
          << "Called value: " << *CS.getCalledValue () << "\n"
          << "In: " << *CS.getInstruction ()->getParent () << "\n"
          << "Of: "
          << CS.getInstruction ()->getParent ()->getParent ()->getName () << "\n";

          errs ()
          << "stripPtr:" << *CS.getCalledValue ()->stripPointerCasts () << "\n"
          << "type: " << *PTy << "\n"
          << "etype: " << *pointeeCSTy << "\n";

          errs () << "cvtype:" << *CS.getCalledValue ()->getType () << "\n";
          );
    }

    if (!pointeeCSTy) return;

    if (FunctionType* FTy = dyn_cast<FunctionType> (pointeeCSTy)) {
      auto it = signatureMap.find (FTy);
      if (it != signatureMap.end ())
      {
        LOG("devirt",
            errs () << "CallSite: " << *CS.getInstruction () << "\n";
            errs () << "Targets for signature: " << *FTy << " are:\n";
            for (auto t : it->second)
              errs () << "\t" << *t << "\n";);
        
        Targets.insert (Targets.end (), it->second.begin (), it->second.end ());
      }
    }
  }

  //
  // Method: findInCache()
  //
  // Description:
  //  This method looks through the cache of bounce functions to see if there
  //  exists a bounce function for the specified call site.
  //
  // Return value:
  //  0 - No usable bounce function has been created.
  //  Otherwise, a pointer to a bounce that can replace the call site is
  //  returned.
  //
  const Function *
  DevirtualizeFunctions::findInCache (const CallSite & CS, func_set_t& Targets) {
    //
    // Iterate through all of the existing bounce functions to see if one of them
    // can be resued.
    //
    DenseMap<const Function *, func_set_t>::iterator I;
    for (I = bounceCache.begin(); I != bounceCache.end(); ++I) {
      // If the bounce function and the function pointer have different types,
      // then skip this bounce function because it is incompatible.
      const Function * bounceFunc = I->first;
      
      // Check the return type
      if (CS.getType() != bounceFunc->getReturnType())
        continue;
      
      // Check the type of the function pointer and the arguments
      if (CS.getCalledValue()->stripPointerCasts()->getType() !=
          bounceFunc->arg_begin()->getType())
        continue;
      
      // Determine whether the targets are identical.  If so, then this function
      // can be used as a bounce function for this call site.
      if (Targets == I->second)
        return I->first;
    }

    //
    // No suiteable bounce function was found.
    //
    return 0;
  }

  //
  // Method: buildBounce()
  //
  // Description:
  //  Replaces the given call site with a call to a bounce function.  The
  //  bounce function compares the function pointer to one of the given
  //  target functions and calls the function directly if the pointer
  //  matches.
  //
  Function*
  DevirtualizeFunctions::buildBounce (CallSite CS,
                                      std::vector<const Function*>& Targets) {
    ++FuncAdded;

    LOG("devirt",
        errs () << "Building a bounce for call site: "
        << *CS.getInstruction () << " using:\n";
        for (auto &f : Targets)
          errs () << "\t" << f->getName () << "\n";);
    
    
    // Create a bounce function that has a function signature almost
    // identical to the function being called.  The only difference is
    // that it will have an additional pointer argument at the
    // beginning of its argument list that will be the function to
    // call.
    Value* ptr = CS.getCalledValue();
    std::vector<Type *> TP;
    TP.insert (TP.begin(), ptr->getType());
    for (CallSite::arg_iterator i = CS.arg_begin();
         i != CS.arg_end();
         ++i) {
      TP.push_back ((*i)->getType());
    }
    
    FunctionType* NewTy = FunctionType::get(CS.getType(), TP, false);
    Module * M = CS.getInstruction()->getParent()->getParent()->getParent();
    Function* F = Function::Create (NewTy,
                                    GlobalValue::InternalLinkage,
                                    "devirtbounce",
                                    M);
    
    // Set the names of the arguments.  Also, record the arguments in a vector
    // for subsequence access.
    F->arg_begin()->setName("funcPtr");
    std::vector<Value*> fargs;
    for(Function::arg_iterator ai = F->arg_begin(), ae = F->arg_end(); ai != ae; ++ai)
      if (ai != F->arg_begin()) {
        fargs.push_back(ai);
        ai->setName("arg");
      }
    
    // Create an entry basic block for the function.  All it should do is perform
    // some cast instructions and branch to the first comparison basic block.
    BasicBlock* entryBB = BasicBlock::Create (M->getContext(), "entry", F);
    
    // For each function target, create a basic block that will call that
    // function directly.
    DenseMap<const Function*, BasicBlock*> targets;
    for (unsigned index = 0; index < Targets.size(); ++index) {
      const Function* FL = Targets[index];
      
      // Create the basic block for doing the direct call
      BasicBlock* BL = BasicBlock::Create (M->getContext(), FL->getName(), F);
      targets[FL] = BL;
      // Create the direct function call
      CallInst* directCall = CallInst::Create (const_cast<Function*>(FL),
                                            fargs,
                                            "",
                                            BL);
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
    
    // Create a failure basic block.  This basic block should simply be an
    // unreachable instruction.
    BasicBlock * failBB = BasicBlock::Create (M->getContext(),
                                              "fail",
                                              F);
    new UnreachableInst (M->getContext(), failBB);
    
    // Setup the entry basic block.  For now, just have it call the failure
    // basic block.  We'll change the basic block to which it branches later.
    BranchInst * InsertPt = BranchInst::Create (failBB, entryBB);
    
    // Create basic blocks which will test the value of the incoming function
    // pointer and branch to the appropriate basic block to call the function.
    Type * VoidPtrType = getVoidPtrType (M->getContext());
    Value * FArg = castTo (F->arg_begin(), VoidPtrType, "", InsertPt);
    BasicBlock * tailBB = failBB;
    for (unsigned index = 0; index < Targets.size(); ++index) {
      // Cast the function pointer to an integer.  This can go in the entry
      // block.
      Value * TargetInt = castTo (const_cast<Function*>(Targets[index]),
                                  VoidPtrType,
                                  "",
                                  InsertPt);
      
      // Create a new basic block that compares the function pointer to the
      // function target.  If the function pointer matches, we'll branch to the
      // basic block performing the direct call for that function; otherwise,
      // we'll branch to the next function call target.
      BasicBlock* TB = targets[Targets[index]];
      BasicBlock* newB = BasicBlock::Create (M->getContext(),
                                             "test." + Targets[index]->getName(),
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
    //InsertPt->setUnconditionalDest (tailBB);
    InsertPt->setSuccessor(0, tailBB);
    //InsertPt->setSuccessor(1, tailBB);

    // Return the newly created bounce function.
    return F;
  }


  //
  // Method: makeDirectCall()
  //
  // Description:
  //  Transform the specified call site into a direct call.
  //
  // Inputs:
  //  CS - The call site to transform.
  //
  // Preconditions:
  //  This method assumes that CS is an indirect call site.
  //
  void
  DevirtualizeFunctions::makeDirectCall (CallSite & CS) {
    //
    // Find the targets of the indirect function call.
    //

    // Convert the call site if there were any function call targets found.
    std::vector<const Function*> Targets;
    findTargets (CS, Targets);

    // No targets found ...
    if (Targets.empty ()) return;

    // Determine if an existing bounce function can be used for this call site.
    func_set_t targetSet (Targets.begin(), Targets.end());
    const Function * NF = findInCache (CS, targetSet);
    
    // If no cached bounce function was found, build a function which will
    // implement a switch statement.  The switch statement will determine which
    // function target to call and call it.
    if (!NF) {
      // Build the bounce function and add it to the cache
      NF = buildBounce (CS, Targets);
      bounceCache[NF] = targetSet;
    }
    
    // Replace the original call with a call to the bounce function.
    if (CallInst* CI = dyn_cast<CallInst>(CS.getInstruction())) {
      // The last operand in the op list is the callee
      // std::vector<Value*> Params (CI->op_begin(), CI->op_end());
      std::vector<Value*> Params;
      Params.reserve (std::distance (CI->op_begin(), CI->op_end()));
      Params.push_back (*(CI->op_end () - 1));
      Params.insert (Params.end (), CI->op_begin(), (CI->op_end() - 1));
      std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
      CallInst* CN = CallInst::Create (const_cast<Function*>(NF),
                                       Params,
                                       name,
                                       CI);
      
      // update call graph
      if (CG) {
        CG->getOrInsertFunction (const_cast<Function*> (NF));
        (*CG)[CI->getParent ()->getParent ()]->addCalledFunction (CallSite (CN),
                                                                  (*CG)[CN->getCalledFunction ()]);
      }

      CN->setDebugLoc (CI->getDebugLoc ());
      CI->replaceAllUsesWith(CN);
      CI->eraseFromParent();
    } else if (InvokeInst* CI = dyn_cast<InvokeInst>(CS.getInstruction())) {
      std::vector<Value*> Params (CI->op_begin(), CI->op_end());
      std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
      InvokeInst* CN = InvokeInst::Create(const_cast<Function*>(NF),
                                          CI->getNormalDest(),
                                          CI->getUnwindDest(),
                                          Params,
                                          name,
                                          CI);
      // TODO: update call graph
      CN->setDebugLoc (CI->getDebugLoc ());
      CI->replaceAllUsesWith(CN);
      CI->eraseFromParent();
    }
    
    ++CSConvert;
    return;
  }

  //
  // Method: visitCallSite()
  //
  // Description:
  //  Examine the specified call site.  If it is an indirect call, mark it for
  //  transformation into a direct call.
  //
  void
  DevirtualizeFunctions::visitCallSite (CallSite &CS) {
    Value * CalledValue = CS.getCalledValue();
    if (isa<Function>(CalledValue->stripPointerCasts()))
      return;
    
    // This is an indirect call site.  Put it in the worklist of call
    // sites to transforms.
    Worklist.push_back (CS.getInstruction());
    return;
  }

  bool DevirtualizeFunctions::runOnModule (Module & M) {

    // Get information on the target system.
    TD = &getAnalysis<DataLayoutPass>().getDataLayout ();

    // Get call graph
    CallGraphWrapperPass *cgwp = getAnalysisIfAvailable<CallGraphWrapperPass> ();
    if (cgwp)
      CG = &cgwp->getCallGraph ();

    // Populate signature map
    for (auto const &F: M) {
      if (F.isIntrinsic ()) continue;
      // -- local functions whose address is not taken cannot be
      // -- resolved by a function pointer
      if (F.hasLocalLinkage () && !F.hasAddressTaken ()) continue;

      // -- skip useless declarations
      if (F.getName().startswith ("seahorn.")) continue;
      if (F.getName().startswith ("verifier.")) continue;

      auto it = signatureMap.find (F.getFunctionType ());
      if (it != signatureMap.end ()) {
        std::vector<const Function*>& fs = it->second;
        fs.push_back (&F);
      }
      else {
        std::vector<const Function*> fs;
        fs.push_back (&F);
        signatureMap.insert (std::make_pair (F.getFunctionType (), fs));
      }
    }

    // Visit all of the call instructions in this function and record those that
    // are indirect function calls.
    visit (M);
    
    // Now go through and transform all of the indirect calls that we found that
    // need transforming.
    for (unsigned index = 0; index < Worklist.size(); ++index) {
      CallSite CS (Worklist[index]);
      makeDirectCall (CS);
    }

    // Conservatively assume that we've changed one or more call sites.
    return true;
  }
  
  Pass* createDevirtualizeFunctionsPass () {
    return new DevirtualizeFunctions ();
  }

  // Pass registration
  RegisterPass<DevirtualizeFunctions>
  XX ("devirt-functions", "Devirtualize indirect function calls using only types");

} // end namespace



