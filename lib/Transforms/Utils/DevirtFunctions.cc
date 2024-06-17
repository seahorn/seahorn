#define DEBUG_TYPE "devirt-functions"

#include "seahorn/Transforms/Utils/DevirtFunctions.hh"
#include "seahorn/Analysis/ClassHierarchyAnalysis.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "seahorn/Transforms/Utils/Local.hh"

#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Transforms/Utils/CallPromotionUtils.h"

#include "seadsa/CompleteCallGraph.hh"

#undef DEBUG_TYPE
#define DEBUG_TYPE "devirt"

using namespace llvm;
using namespace seadsa;

namespace seahorn {

static bool isIndirectCall(CallBase &CB) {
  Value *v = CB.getCalledOperand();
  if (!v)
    return false;

  v = v->stripPointerCastsAndAliases();
  return !isa<Function>(v);
}

///
/// Create a sequence of if-then-else statements at the location of
/// the callsite.  The "if" condition compares the callsite's called
/// value with a function f from Callees.  The direct call to f is
/// moved to the "then" block. The "else" block contains the next
/// "if". For the last callsite's called value we don't create an
/// "else" block if keepOriginalCallSite is false. Otherwise, the last
/// "else" block contains the original call site.
///
/// For example, the call instruction below:
///
///   orig_bb:
///     %t0 = call i32 %ptr()  with callees = {foo, bar}
///     ...
///
/// Is replaced by the following:
///
///   orig_bb:
///     %cond = icmp eq i32 ()* %ptr, @foo
///     br i1 %cond, %then_bb, %else_bb
///
///   then_bb:
///     %t1 = call i32 @foo()
///     br merge_bb
///
///   else_bb:
///     %t0 = call i32 %bar()
///     br merge_bb
///
///   merge_bb:
///     ; Uses of the original call instruction are replaced by uses of the phi
///     ; node.
///     %t2 = phi i32 [ %t0, %else_bb ], [ %t1, %then_bb ]
///     ...
///
static void promoteIndirectCall(CallBase &CB,
                                const std::vector<Function *> &Callees,
                                bool keepOriginalCall) {
  for (unsigned i = 0, numCallees = Callees.size(); i < numCallees; ++i) {
    if (i == numCallees - 1 && !keepOriginalCall) {
      llvm::promoteCall(CB, Callees[i]);
    } else {
      llvm::promoteCallWithIfThenElse(CB, Callees[i]);
    }
  }
}

namespace devirt_impl {

AliasSetId typeAliasId(CallBase &CB) {
  assert(isIndirectCall(CB) && "Not an indirect call");
  PointerType *pTy = dyn_cast<PointerType>(CB.getCalledOperand()->getType());
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
    AliasSet &Targets = m_targets_map[devirt_impl::typeAliasId(F)];
    // XXX: ordered by pointer addresses. Ideally we should use
    // something more deterministic.
    auto it = std::upper_bound(Targets.begin(), Targets.end(), &F);
    Targets.insert(it, &F);
  }
}

const CallSiteResolverByTypes::AliasSet *
CallSiteResolverByTypes::getTargets(CallBase &CB, bool &isComplete) {
  AliasSetId id = devirt_impl::typeAliasId(CB);
  isComplete = false;
  auto it = m_targets_map.find(id);
  if (it != m_targets_map.end()) {
    return &it->second;
  } else {
    LOG("devirt", errs() << "Target not found for id=" << *id << "\n";);
    for (auto ptr = m_targets_map.begin(); ptr != m_targets_map.end(); ++ptr) {
      LOG("devirt", errs() << "id found:" << *ptr->first << "\n";);
    }

    // This shouldn't happen
    return nullptr;
  }
}

#ifdef USE_BOUNCE_FUNCTIONS
Function *CallSiteResolverByTypes::getBounceFunction(CallBase &CB) {
  AliasSetId id = devirt_impl::typeAliasId(CB);
  auto it = m_bounce_map.find(id);
  if (it != m_bounce_map.end()) {
    return it->second;
  } else {
    return nullptr;
  }
}

void CallSiteResolverByTypes::cacheBounceFunction(CallBase &CB,
                                                  Function *bounce) {
  AliasSetId id = devirt_impl::typeAliasId(CB);
  m_bounce_map.insert({id, bounce});
}
#endif

/** end Resolver by only types */

/** begin Resolver by dsa+types */
CallSiteResolverByDsa::CallSiteResolverByDsa(Module &M,
                                             CompleteCallGraphAnalysis &dsa)
    : CallSiteResolver(CallSiteResolverKind::RESOLVER_SEADSA), m_M(M),
      m_dsa(dsa) {

  CallSiteResolver::m_kind = CallSiteResolverKind::RESOLVER_SEADSA;
  // build the target map
  unsigned num_indirect_calls = 0;
  unsigned num_complete_calls = 0;
  unsigned num_resolved_calls = 0;

  for (auto &F : m_M) {
    for (auto &I : instructions(&F)) {
      if (!isa<CallInst>(&I) && !isa<InvokeInst>(&I))
        continue;
      auto &CB = *dyn_cast<CallBase>(&I);
      if (isIndirectCall(CB)) {
        num_indirect_calls++;
        num_complete_calls += m_dsa.isComplete(CB);

        AliasSet dsa_targets;
        dsa_targets.append(m_dsa.begin(CB), m_dsa.end(CB));

        if (dsa_targets.empty()) {
          DOG(WARN << "Devirt(dsa) no DSA call target for "
                   << "\n\t" << CB << "\n"
                   << " in @" << F.getName(););
          continue;
        }
        std::sort(dsa_targets.begin(), dsa_targets.end());
        num_resolved_calls++;
        m_targets_map.insert({&CB, dsa_targets});
        DOG({
          INFO << "Devirt (dsa): resolved " << CB << " with targets:";
          for (auto F : dsa_targets) {
            INFO << "\t@" << F->getName();
          }
        });
      }
    }
  }
  (void)num_complete_calls;
}

const CallSiteResolverByDsa::AliasSet *
CallSiteResolverByDsa::getTargets(CallBase &CB, bool &isComplete) {
  isComplete = m_dsa.isComplete(CB);
  auto it = m_targets_map.find(&CB);
  if (it != m_targets_map.end()) {
    return &it->second;
  } else {
    return nullptr;
  }
}

#ifdef USE_BOUNCE_FUNCTIONS
Function *CallSiteResolverByDsa::getBounceFunction(CallBase &CB) {
  AliasSetId id = devirt_impl::typeAliasId(CB);
  auto it = m_bounce_map.find(id);
  if (it != m_bounce_map.end()) {
    const AliasSet *cachedTargets = it->second.first;
    bool isComplete; /*unused*/
    const AliasSet *Targets = getTargets(CB, isComplete);
    if (cachedTargets && Targets) {
      if (std::equal(cachedTargets->begin(), cachedTargets->end(),
                     Targets->begin())) {
        return it->second.second;
      }
    }
  }
  return nullptr;
}

void CallSiteResolverByDsa::cacheBounceFunction(CallBase &CB,
                                                Function *bounce) {
  bool isComplete; /*unused*/
  const AliasSet *Targets = getTargets(CB, isComplete);
  if (Targets) {
    AliasSetId id = devirt_impl::typeAliasId(CB);
    m_bounce_map.insert({id, {Targets, bounce}});
  }
}
#endif

/** end Resolver by dsa+types */

/** begin Resolver by class hierarchy analysis */
CallSiteResolverByCHA::CallSiteResolverByCHA(Module &M)
    : CallSiteResolver(CallSiteResolverKind::RESOLVER_CHA),
      m_cha(std::make_unique<ClassHierarchyAnalysis>(M)) {
  m_cha->calculate();

  DOG(m_cha->printClassHierarchy(errs()); m_cha->printVtables(errs()););
}

CallSiteResolverByCHA::~CallSiteResolverByCHA() = default;

const CallSiteResolverByCHA::AliasSet *
CallSiteResolverByCHA::getTargets(CallBase &CB, bool &isComplete) {
  if (!m_cha->isVCallResolved(CB)) {
    isComplete = false;
    return nullptr;
  }

  isComplete = true;
  return &(m_cha->getVCallCallees(CB));
}

#ifdef USE_BOUNCE_FUNCTIONS
Function *CallSiteResolverByCHA::getBounceFunction(CallBase &CB) {
  // Caching not implemented.
  // Caching cannot be based only on the function type signature. This
  // is because two different virtual calls to different methods can
  // have the same types.
  return nullptr;
}

void CallSiteResolverByCHA::cacheBounceFunction(CallBase &CB,
                                                Function *bounce) {
  // do nothing for now
}
#endif

/** end Resolver by class hierarchy analysis */

/***
 * End specific callsites resolver
 ***/

DevirtualizeFunctions::DevirtualizeFunctions(llvm::CallGraph *cg,
                                             bool allowIndirectCalls)
    : m_cg(cg), m_allowIndirectCalls(allowIndirectCalls) {
  (void)m_cg;
}

DevirtualizeFunctions::~DevirtualizeFunctions() {}

void DevirtualizeFunctions::visitCallBase(CallBase &CB) {
  // -- skip direct calls
  if (!isIndirectCall(CB))
    return;
  LOG("devirt", errs() << "Pushing to worklist: " << CB << "\n";);

  // This is an indirect call site.  Put it in the worklist of call
  // sites to transforms.
  m_worklist.push_back(&CB);
}

void DevirtualizeFunctions::visitCallInst(CallInst &CI) {
  // we cannot take the address of an inline asm
  if (CI.isInlineAsm())
    return;
  LOG("devirt", errs() << "Visiting callbase: " << CI << "\n";);
  visitCallBase(CI);
}

void DevirtualizeFunctions::visitInvokeInst(InvokeInst &II) {
  visitCallBase(II);
}

#ifdef USE_BOUNCE_FUNCTIONS
/**
 * Creates a bounce function that calls functions in an alias set directly
 * All the work happens here.
 */
Function *DevirtualizeFunctions::mkBounceFn(CallBase &CB,
                                            CallSiteResolver *CSR) {
  assert(isIndirectCall(CB) && "Not an indirect call");

  // We don't create a bounce function if the function has a
  // variable number of arguments.
  if (CB.getFunctionType()->isVarArg()) {
    return nullptr;
  }

  if (Function *bounce = CSR->getBounceFunction(CB)) {
    DOG(errs() << "Reusing bounce function for " << CB << "\n\t"
               << bounce->getName() << "::" << *(bounce->getType()) << "\n";);
    return bounce;
  }

  bool isComplete;
  const AliasSet *Targets = CSR->getTargets(CB, isComplete);
  if (!Targets || Targets->empty()) {
    // cannot resolve the indirect call
    return nullptr;
  }

  DOG({
    errs() << "Building a bounce for call site:\n" << CB << " using:\n";
    for (auto &f : *Targets) {
      errs() << "\t" << f->getName() << " :: " << *(f->getType()) << "\n";
    }
  });

  // Create a bounce function that has a function signature almost
  // identical to the function being called.  The only difference is
  // that it will have an additional pointer argument at the
  // beginning of its argument list that will be the function to
  // call.
  Value *ptr = CB.getCalledOperand();
  SmallVector<Type *, 8> TP;
  TP.push_back(ptr->getType());
  for (auto i = CB.data_operands_begin(), e = CB.data_operands_end(); i != e;
       ++i)
    TP.push_back((*i)->getType());

  FunctionType *NewTy = FunctionType::get(CS.getType(), TP, false);
  Module *M = &CB->getParent()->getParent()->getParent();
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
      fl_cg->addCalledFunction(directCall, cf_cg);
    }

    // Add the return instruction for the basic block
    if (CB.getType()->isVoidTy())
      ReturnInst::Create(M->getContext(), BL);
    else
      ReturnInst::Create(M->getContext(), directCall, BL);
  }

  // Create a default basic block having the original indirect call
  BasicBlock *defaultBB = BasicBlock::Create(M->getContext(), "default", F);

  if (CB.getType()->isVoidTy()) {
    ReturnInst::Create(M->getContext(), defaultBB);
  } else {
    Value *defaultRet = nullptr;
    if (!isComplete && m_allowIndirectCalls) {
      defaultRet = CallInst::Create(&*(F->arg_begin()), fargs, "", defaultBB);
      ReturnInst::Create(M->getContext(), defaultRet, defaultBB);
    } else {
      // -- Create an external function that abstracts the behavior of
      // -- the original indirect call.
      // Function &fn = createNewNondetFn (*M, *CB.getType (), 1,
      // "nondet.bounce.fptr."); defaultRet = CallInst::Create (&fn, "",
      // defaultBB); ReturnInst::Create (M->getContext(), defaultRet,
      // defaultBB);

      // -- Assume no missing callees so we making unreachable the
      // -- default case.
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
  CSR->cacheBounceFunction(CB, F);

  // if (enable_caching) {
  //   // -- log the newly created function
  //   m_bounceMap.insert(std::make_pair(id, F));
  // }

  // Return the newly created bounce function.
  return F;
}
#endif

void DevirtualizeFunctions::mkDirectCall(CallBase &CB, CallSiteResolver *CSR) {
#ifndef USE_BOUNCE_FUNCTIONS
  bool isComplete;
  const AliasSet *Targets = CSR->getTargets(CB, isComplete);
  if (!Targets || Targets->empty()) {
    // cannot resolve the indirect call
    LOG("devirt", errs() << "Target not found for call" << CB << "\n";);
    return;
  }
  LOG("devirt", errs() << "Creating bounce fn: " << CB << "\n";);

  DOG({
    errs() << "Resolving indirect call site:\n" << CB << " using:\n";
    for (auto &f : *Targets) {
      errs() << "\t" << f->getName() << " :: " << *(f->getType()) << "\n";
    }
  });

  // HACK: remove constness
  std::vector<Function *> Callees;
  Callees.resize(Targets->size());
  std::transform(Targets->begin(), Targets->end(), Callees.begin(),
                 [](const Function *fn) { return const_cast<Function *>(fn); });
  // promote indirect call to a bunch of direct calls
  promoteIndirectCall(CB, Callees, !isComplete && m_allowIndirectCalls);
#else
  const Function *bounceFn = mkBounceFn(CB, CSR);
  // -- something failed
  DOG({
    if (!bounceFn)
      errs() << "No bounce function for: " << CB << "\n";
  });

  if (!bounceFn)
    return;

  // Replace the original call with a call to the bounce function.
  if (CallInst *CI = dyn_cast<CallInst>(&CB)) {
    LOG("devirt", errs() << "Processing callinst: " << CI << "\n";);

    // The last operand in the op list is the callee
    SmallVector<Value *, 8> Params;
    Params.reserve(std::distance(CI->op_begin(), CI->op_end()));
    Params.push_back(*(CI->op_end() - 1));
    Params.insert(Params.end(), CI->op_begin(), (CI->op_end() - 1));
    std::string name = CI->hasName() ? CI->getName().str() + ".dv" : "";
    CallInst *CN =
        CallInst::Create(const_cast<Function *>(bounceFn), Params, name, CI);

    DOG(errs() << "Call to bounce function: \n" << *CN << "\n";);

    // update call graph
    if (m_cg) {
      m_cg->getOrInsertFunction(const_cast<Function *>(bounceFn));
      (*m_cg)[CI->getParent()->getParent()]->addCalledFunction(
          CN, (*m_cg)[CN->getCalledFunction()]);
    }

    CN->setDebugLoc(CI->getDebugLoc());
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  } else if (InvokeInst *CI = dyn_cast<InvokeInst>(&CB)) {
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
    DOG(errs() << "Call to bounce function: \n" << *CN << "\n";);

    // update call graph
    if (m_cg) {
      m_cg->getOrInsertFunction(const_cast<Function *>(bounceFn));
      (*m_cg)[CI->getParent()->getParent()]->addCalledFunction(
          CN, (*m_cg)[CN->getCalledFunction()]);
    }

    CN->setDebugLoc(CI->getDebugLoc());
    CI->replaceAllUsesWith(CN);
    CI->eraseFromParent();
  }
#endif
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
    mkDirectCall(*cast<CallBase>(I), CSR);
  }

  // Conservatively assume that we've changed one or more call sites.
  return Changed;
}

} // namespace seahorn
