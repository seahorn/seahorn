#define DEBUG_TYPE "devirt-functions"

#include "seahorn/Transforms/Utils/DevirtFunctions.hh"
#include "seahorn/Analysis/ClassHierarchyAnalysis.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Transforms/Utils/Local.hh"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/InstIterator.h"

#include "sea_dsa/CompleteCallGraph.hh"

using namespace llvm;
using namespace sea_dsa;

namespace seahorn {

static bool isIndirectCall(CallSite &CS) {
  Value *v = CS.getCalledValue();
  if (!v)
    return false;

  v = v->stripPointerCasts();
  return !isa<Function>(v);
}

static inline PointerType *getVoidPtrType(LLVMContext &C) {
  Type *Int8Type = IntegerType::getInt8Ty(C);
  return PointerType::getUnqual(Int8Type);
}

static inline Value *castTo(Value *V, Type *Ty, std::string Name,
                            Instruction *InsertPt) {
  // Don't bother creating a cast if it's already the correct type.
  if (V->getType() == Ty)
    return V;

  // If it's a constant, just create a constant expression.
  if (Constant *C = dyn_cast<Constant>(V)) {
    Constant *CE = ConstantExpr::getZExtOrBitCast(C, Ty);
    return CE;
  }

  // Otherwise, insert a cast instruction.
  return CastInst::CreateZExtOrBitCast(V, Ty, Name, InsertPt);
}

namespace devirt_impl {

AliasSetId typeAliasId(CallSite &CS) {
  assert(isIndirectCall(CS) && "Not an indirect call");
  PointerType *pTy = dyn_cast<PointerType>(CS.getCalledValue()->getType());
  assert(pTy && "Unexpected call not through a pointer");
  assert(isa<FunctionType>(pTy->getElementType()) &&
         "The type of called value is not a pointer to a function");
  return pTy;
}

AliasSetId typeAliasId(const Function &F) {
  return F.getFunctionType()->getPointerTo();
}

} // namespace devirt_impl

/***
 * Begin specific callsites resolvers
 ***/


/** begin Resolver by only types */
CallSiteResolverByTypes::CallSiteResolverByTypes(Module &M)
  : CallSiteResolver(CallSiteResolverKind::RESOLVER_TYPES), m_M(M) {
  populateTypeAliasSets();
}

CallSiteResolverByTypes::~CallSiteResolverByTypes() = default;

void CallSiteResolverByTypes::populateTypeAliasSets() {
  // -- Create type-based alias sets
  for (auto const &F : m_M) {
    // -- intrinsics are never called indirectly
    if (F.isIntrinsic())
      continue;

    // -- local functions whose address is not taken cannot be
    // -- resolved by a function pointer
    if (F.hasLocalLinkage() && !F.hasAddressTaken())
      continue;

    // -- skip calls to declarations, these are resolved implicitly
    // -- by calling through the function pointer argument in the
    // -- default case of bounce function
    if (F.isDeclaration())
      continue;

    // -- skip seahorn and verifier specific intrinsics
    if (F.getName().startswith("seahorn."))
      continue;
    if (F.getName().startswith("verifier."))
      continue;
    // -- assume entry point is never called indirectly
    if (F.getName().equals("main"))
      continue;

    // -- add F to its corresponding alias set (keep sorted the Targets)
    AliasSet& Targets = m_targets_map[devirt_impl::typeAliasId(F)];    
    // XXX: ordered by pointer addresses. Ideally we should use
    // something more deterministic.
    auto it = std::upper_bound(Targets.begin(), Targets.end(), &F);
    Targets.insert(it, &F);
  }
}

const CallSiteResolverByTypes::AliasSet*
CallSiteResolverByTypes::getTargets(CallSite &CS)  {
  AliasSetId id = devirt_impl::typeAliasId(CS);
  auto it = m_targets_map.find(id);
  if (it != m_targets_map.end()) {
    return &it->second;
  } else {
    return nullptr;
  }
}

Function* CallSiteResolverByTypes::getBounceFunction(CallSite& CS) {
  AliasSetId id = devirt_impl::typeAliasId(CS);
  auto it = m_bounce_map.find(id);
  if (it != m_bounce_map.end()) {
    return it->second;
  } else {
    return nullptr;
  }
}

void CallSiteResolverByTypes::cacheBounceFunction(CallSite&CS, Function* bounce) {
  AliasSetId id = devirt_impl::typeAliasId(CS);    
  m_bounce_map.insert({id, bounce});
}
/** end Resolver by only types */

/** begin Resolver by dsa+types */
CallSiteResolverByDsa::CallSiteResolverByDsa(Module& M,
					     CompleteCallGraphAnalysis& dsa,
					     bool incomplete)
  : CallSiteResolverByTypes(M)
  , m_M(M), m_dsa(dsa), m_allow_incomplete(incomplete) {
    
  CallSiteResolver::m_kind = CallSiteResolverKind::RESOLVER_SEA_DSA;
  
  // build the target map
  unsigned num_indirect_calls = 0;
  unsigned num_complete_calls = 0;
  unsigned num_resolved_calls = 0;
  
  for (auto &F: m_M) {
    for (auto &I: llvm::make_range(inst_begin(&F), inst_end(&F))) {
      if (!isa<CallInst>(&I) && !isa<InvokeInst>(&I))
	continue;
      CallSite CS(&I);
      if (isIndirectCall(CS)) {
	num_indirect_calls++;
	if (m_allow_incomplete || m_dsa.isComplete(CS)) {
	  num_complete_calls++;
	  AliasSet dsa_targets;
	  dsa_targets.append(m_dsa.begin(CS), m_dsa.end(CS));
	  if (dsa_targets.empty()) {
	    //m_stats.m_num_dsa_unresolved++;
	    LOG("devirt", errs()
		<< "WARNING Devirt (dsa): does not have any target for "
		<< *(CS.getInstruction()) << "\n";);
	    continue;
	  }
	  std::sort(dsa_targets.begin(), dsa_targets.end());
	  
	  LOG("devirt",
	      errs() << "\nDsa-based targets: \n";
	      for(auto F: dsa_targets) {
		errs() << "\t" << F->getName() << "::" << *(F->getType()) << "\n";
	      });

	  const AliasSet* types_targets = CallSiteResolverByTypes::getTargets(CS);
	  if (types_targets && !types_targets->empty()) {
	    
	    LOG("devirt",
		errs() << "Type-based targets: \n";
		for(auto F: *types_targets) {
		  errs() << "\t" << F->getName() << "::" << *(F->getType())
			 << "\n";
		});
	    
	    // --- We filter out those dsa targets whose signature do not match.
	    AliasSet refined_dsa_targets;
	    std::set_intersection(dsa_targets.begin(), dsa_targets.end(),
				  types_targets->begin(), types_targets->end(),
				  std::back_inserter(refined_dsa_targets));
	    if (refined_dsa_targets.empty()) {
	      //m_stats.m_num_type_unresolved++;		  		    
	      LOG("devirt",
		  errs() << "WARNING Devirt (dsa): cannot resolve "
		         << *(CS.getInstruction())
		         << " after refining dsa targets with callsite type\n";);
	    } else {
	      num_resolved_calls++;
	      m_targets_map.insert({CS.getInstruction(), refined_dsa_targets});
	      LOG("devirt",
		  errs() << "Devirt (dsa) resolved " << *(CS.getInstruction())
		         << " with targets: \n";
		  for(auto F: refined_dsa_targets) {
		    errs() << "\t" << F->getName() << "::"
			   << *(F->getType()) << "\n";  
		  });
	    }
	  } else {
	    //m_stats.m_num_type_unresolved++;		  
	    LOG("devirt",
		errs() << "WARNING Devirt (dsa): cannot resolve "
		       << *(CS.getInstruction())
		       << " because there is no function with same callsite type\n";);
	  }
	} else {
	  //m_stats.m_num_dsa_unresolved++;
	  LOG("devirt",
	      errs() << "WARNING Devirt (dsa): cannot resolve "
	             << *(CS.getInstruction())
	             << " because the corresponding dsa node is not complete\n";
	      
	      AliasSet targets;
	      targets.append(m_dsa.begin(CS), m_dsa.end(CS));
	      errs() << "Dsa-based targets: \n";
	      for(auto F: targets) {
		errs() << "\t" << F->getName() << "::" << *(F->getType()) << "\n";
	      };);
	}
      }
    }
  }
}
  
const CallSiteResolverByDsa::AliasSet*
CallSiteResolverByDsa::getTargets(CallSite& CS) {
  auto it = m_targets_map.find(CS.getInstruction());
  if (it != m_targets_map.end()) {
    return &it->second;
  } else {
    return nullptr;
  }
}

Function* CallSiteResolverByDsa::getBounceFunction(CallSite&CS) {
  AliasSetId id = devirt_impl::typeAliasId(CS);
  auto it = m_bounce_map.find(id);
  if (it != m_bounce_map.end()) {
    const AliasSet* cachedTargets = it->second.first;
    const AliasSet* Targets = getTargets(CS);
    if (cachedTargets && Targets) {
      if (std::equal(cachedTargets->begin(), cachedTargets->end(),
		     Targets->begin())) {
	return it->second.second;
      }
    }
  }
  return nullptr;
}
  
void CallSiteResolverByDsa::cacheBounceFunction(CallSite& CS, Function* bounce) {
  const AliasSet* Targets = getTargets(CS);
  if (Targets) {
    AliasSetId id = devirt_impl::typeAliasId(CS);      
    m_bounce_map.insert({id, {Targets, bounce}});
  }
}
/** end Resolver by dsa+types */

/** begin Resolver by class hierarchy analysis */
CallSiteResolverByCHA::CallSiteResolverByCHA(Module &M)
    : CallSiteResolver(CallSiteResolverKind::RESOLVER_CHA),
      m_cha(make_unique<ClassHierarchyAnalysis>(M)) {
  m_cha->calculate();

  LOG("devirt", m_cha->printClassHierarchy(errs());
      m_cha->printVtables(errs()););
}

CallSiteResolverByCHA::~CallSiteResolverByCHA() = default;

const CallSiteResolverByCHA::AliasSet*
CallSiteResolverByCHA::getTargets(CallSite &CS) {
  ImmutableCallSite ICS(CS.getInstruction());
  if (!m_cha->isVCallResolved(ICS))
    return nullptr;

  return &(m_cha->getVCallCallees(ICS));
}

Function* CallSiteResolverByCHA::getBounceFunction(CallSite& CS) {
  // Caching not implemented.
  // Caching cannot be based only on the function type signature. This
  // is because two different virtual calls to different methods can
  // have the same types.
  return nullptr;
}

void CallSiteResolverByCHA::cacheBounceFunction(CallSite&CS, Function* bounce) {
  // do nothing for now
}
/** end Resolver by class hierarchy analysis */

/***
 * End specific callsites resolver
 ***/


DevirtualizeFunctions::DevirtualizeFunctions(llvm::CallGraph *cg,
					     bool allowIndirectCalls)
  : m_cg(cg), m_allowIndirectCalls(allowIndirectCalls) {}

DevirtualizeFunctions::~DevirtualizeFunctions() {} 

void DevirtualizeFunctions::visitCallSite(CallSite &CS) {
  // -- skip direct calls
  if (!isIndirectCall(CS))
    return;

  // This is an indirect call site.  Put it in the worklist of call
  // sites to transforms.
  m_worklist.push_back(CS.getInstruction());
}

void DevirtualizeFunctions::visitCallInst(CallInst &CI) {
  // we cannot take the address of an inline asm
  if (CI.isInlineAsm())
    return;

  CallSite CS(&CI);
  visitCallSite(CS);
}

void DevirtualizeFunctions::visitInvokeInst(InvokeInst &II) {
  CallSite CS(&II);
  visitCallSite(CS);
}

/**
 * Creates a bounce function that calls functions in an alias set directly
 * All the work happens here.
 */
Function *DevirtualizeFunctions::mkBounceFn(CallSite &CS, CallSiteResolver *CSR) {
  assert(isIndirectCall(CS) && "Not an indirect call");

  // We don't create a bounce function if the function has a
  // variable number of arguments.
  if (CS.getFunctionType()->isVarArg()) {
    return nullptr;
  }

  if (Function* bounce = CSR->getBounceFunction(CS)) {
    LOG("devirt",
	errs() << "Reusing bounce function for " << *(CS.getInstruction()) 
	<< "\n\t" << bounce->getName() << "::" << *(bounce->getType()) << "\n";);
    return bounce;
  }
    
  const AliasSet* Targets = CSR->getTargets(CS);
  if (!Targets || Targets->empty()) {
    // cannot resolve the indirect call
    return nullptr;
  }

  LOG("devirt", errs() << "Building a bounce for call site:\n"
                       << *CS.getInstruction() << " using:\n";
      for (auto &f
           : *Targets) {
        errs() << "\t" << f->getName() << " :: " << *(f->getType()) << "\n";
      });

  // Create a bounce function that has a function signature almost
  // identical to the function being called.  The only difference is
  // that it will have an additional pointer argument at the
  // beginning of its argument list that will be the function to
  // call.
  Value *ptr = CS.getCalledValue();
  SmallVector<Type *, 8> TP;
  TP.push_back(ptr->getType());
  for (auto i = CS.arg_begin(), e = CS.arg_end(); i != e; ++i)
    TP.push_back((*i)->getType());

  FunctionType *NewTy = FunctionType::get(CS.getType(), TP, false);
  Module *M = CS.getInstruction()->getParent()->getParent()->getParent();
  assert(M);
  Function *F = Function::Create(NewTy, GlobalValue::InternalLinkage,
                                 "seahorn.bounce", M);

  // Set the names of the arguments.  Also, record the arguments in a vector
  // for subsequence access.
  F->arg_begin()->setName("funcPtr");
  SmallVector<Value *, 8> fargs;
  auto ai = F->arg_begin();
  ++ai;
  for (auto ae = F->arg_end(); ai != ae; ++ai) {
    fargs.push_back(&*ai);
    ai->setName("arg");
  }

  // Create an entry basic block for the function.  All it should do is perform
  // some cast instructions and branch to the first comparison basic block.
  BasicBlock *entryBB = BasicBlock::Create(M->getContext(), "entry", F);

  // For each function target, create a basic block that will call that
  // function directly.
  DenseMap<const Function *, BasicBlock *> targets;
  for (const Function *FL : *Targets) {
    // Create the basic block for doing the direct call
    BasicBlock *BL = BasicBlock::Create(M->getContext(), FL->getName(), F);
    targets[FL] = BL;

    if (CSR->get_kind() == CallSiteResolverKind::RESOLVER_CHA) {
      // For C++ virtual calls, if Targets is generated by a class
      // hierarchy analysis it is possible that the type of the 1st
      // parameter in the callee is different from the type of the 1st
      // parameter at the call site.  This case can occur when at the
      // callsite the type of the object is a superclass of the type
      // of the callee.
      if (!FL->arg_empty()) {
        assert(!fargs.empty());
        auto &callee_arg = *(FL->arg_begin());
        if (fargs[0]->getType() != callee_arg.getType()) {
          fargs[0] = new BitCastInst(fargs[0], callee_arg.getType(),
                                     "casted." + fargs[0]->getName(), BL);
        }
      }
    }

    // Create the direct function call
    CallingConv::ID cc = FL->getCallingConv();
    CallInst *directCall =
        CallInst::Create(const_cast<Function *>(FL), fargs, "", BL);
    directCall->setCallingConv(cc);
    // update call graph
    if (m_cg) {
      auto fl_cg = m_cg->getOrInsertFunction(const_cast<Function *>(FL));
      auto cf_cg = m_cg->getOrInsertFunction(directCall->getCalledFunction());
      fl_cg->addCalledFunction(CallSite(directCall), cf_cg);
    }

    // Add the return instruction for the basic block
    if (CS.getType()->isVoidTy())
      ReturnInst::Create(M->getContext(), BL);
    else
      ReturnInst::Create(M->getContext(), directCall, BL);
  }

  // Create a default basic block having the original indirect call
  BasicBlock *defaultBB = BasicBlock::Create(M->getContext(), "default", F);

  if (CS.getType()->isVoidTy()) {
    ReturnInst::Create(M->getContext(), defaultBB);
  } else {
    Value *defaultRet = nullptr;
    if (m_allowIndirectCalls) {
      defaultRet = CallInst::Create(&*(F->arg_begin()), fargs, "", defaultBB);
      ReturnInst::Create(M->getContext(), defaultRet, defaultBB);
    } else {
      // -- Create an external function that abstracts the behavior of
      // -- the original indirect call.
      // Function &fn = createNewNondetFn (*M, *CS.getType (), 1,
      // "nondet.bounce.fptr."); defaultRet = CallInst::Create (&fn, "",
      // defaultBB); ReturnInst::Create (M->getContext(), defaultRet,
      // defaultBB);

      // -- Assume no missing callees (potentially unsound) so we
      // -- making unreachable the default case.
      new UnreachableInst(M->getContext(), defaultBB);
    }
  }

  // Setup the entry basic block.  For now, just have it call the default
  // basic block.  We'll change the basic block to which it branches later.
  BranchInst *InsertPt = BranchInst::Create(defaultBB, entryBB);

  // Create basic blocks which will test the value of the incoming function
  // pointer and branch to the appropriate basic block to call the function.
  Type *VoidPtrType = getVoidPtrType(M->getContext());
  Value *FArg = castTo(&*(F->arg_begin()), VoidPtrType, "", InsertPt);
  BasicBlock *tailBB = defaultBB;
  for (const Function *FL : *Targets) {

    // Cast the function pointer to an integer.  This can go in the entry
    // block.
    Value *TargetInt =
        castTo(const_cast<Function *>(FL), VoidPtrType, "", InsertPt);

    // Create a new basic block that compares the function pointer to the
    // function target.  If the function pointer matches, we'll branch to the
    // basic block performing the direct call for that function; otherwise,
    // we'll branch to the next function call target.
    BasicBlock *TB = targets[FL];
    BasicBlock *newB =
        BasicBlock::Create(M->getContext(), "test." + FL->getName(), F);
    CmpInst *setcc = CmpInst::Create(Instruction::ICmp, CmpInst::ICMP_EQ,
                                     TargetInt, FArg, "sc", newB);
    BranchInst::Create(TB, tailBB, setcc, newB);

    // Make this newly created basic block the next block that will be reached
    // when the next comparison will need to be done.
    tailBB = newB;
  }

  // Make the entry basic block branch to the first comparison basic block.
  InsertPt->setSuccessor(0, tailBB);

  // -- cache the newly created function
  CSR->cacheBounceFunction(CS, F);

  // if (enable_caching) {
  //   // -- log the newly created function
  //   m_bounceMap.insert(std::make_pair(id, F));
  // }

  // Return the newly created bounce function.
  return F;
}

void DevirtualizeFunctions::mkDirectCall(CallSite CS, CallSiteResolver *CSR) {
  const Function *bounceFn = mkBounceFn(CS, CSR);
  // -- something failed
  LOG("devirt", if (!bounceFn) errs() << "No bounce function for: "
                                      << *CS.getInstruction() << "\n";);

  if (!bounceFn)
    return;

  // Replace the original call with a call to the bounce function.
  if (CallInst *CI = dyn_cast<CallInst>(CS.getInstruction())) {
    // The last operand in the op list is the callee
    SmallVector<Value *, 8> Params;
    Params.reserve(std::distance(CI->op_begin(), CI->op_end()));
    Params.push_back(*(CI->op_end() - 1));
    Params.insert(Params.end(), CI->op_begin(), (CI->op_end() - 1));
    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    CallInst *CN =
        CallInst::Create(const_cast<Function *>(bounceFn), Params, name, CI);

    LOG("devirt", errs() << "Call to bounce function: \n" << *CN << "\n";);

    // update call graph
    if (m_cg) {
      m_cg->getOrInsertFunction(const_cast<Function *>(bounceFn));
      (*m_cg)[CI->getParent()->getParent()]->addCalledFunction(
          CallSite(CN), (*m_cg)[CN->getCalledFunction()]);
    }

    CN->setDebugLoc(CI->getDebugLoc());
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  } else if (InvokeInst *CI = dyn_cast<InvokeInst>(CS.getInstruction())) {
    SmallVector<Value *, 8> Params;
    Params.reserve(
        std::distance(CI->arg_operands().begin(), CI->arg_operands().end()));
    // insert first the callee
    Params.push_back(CI->getCalledValue());
    Params.insert(Params.end(), CI->arg_operands().begin(),
                  CI->arg_operands().end());

    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    InvokeInst *CN = InvokeInst::Create(const_cast<Function *>(bounceFn),
                                        CI->getNormalDest(),
                                        CI->getUnwindDest(), Params, name, CI);

    LOG("devirt", errs() << "Call to bounce function: \n" << *CN << "\n";);

    // update call graph
    if (m_cg) {
      m_cg->getOrInsertFunction(const_cast<Function *>(bounceFn));
      (*m_cg)[CI->getParent()->getParent()]->addCalledFunction(
          CallSite(CN), (*m_cg)[CN->getCalledFunction()]);
    }

    CN->setDebugLoc(CI->getDebugLoc());
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  }

  return;
}

bool DevirtualizeFunctions::resolveCallSites(Module &M, CallSiteResolver *CSR) {

  // Visit all of the call instructions in this function and record those that
  // are indirect function calls.
  visit(M);

  // Now go through and transform all of the indirect calls that we found that
  // need transforming.
  bool Changed = !m_worklist.empty();
  while (!m_worklist.empty()) {
    auto I = m_worklist.back();
    m_worklist.pop_back();
    CallSite CS(I);
    mkDirectCall(CS, CSR);
  }

  // Conservatively assume that we've changed one or more call sites.
  return Changed;
}

} // namespace seahorn
