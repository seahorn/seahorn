#include "seahorn/Analysis/SeaBuiltinsInfo.hh"

#include "seahorn/InitializePasses.hh"
#include "seahorn/Passes.hh"

#include "llvm/IR/Function.h"
#include "llvm/IR/InstrTypes.h"
#include "llvm/IR/Module.h"

#include "llvm/ADT/StringSwitch.h"

using namespace seahorn;
using namespace llvm;

#define VERIFIER_ERROR_FN "verifier.error"
#define SEAHORN_FAIL_FN "seahorn.fail"
#define VERIFIER_ASSUME_FN "verifier.assume"
#define VERIFIER_ASSUME_NOT_FN "verifier.assume.not"
#define VERIFIER_ASSERT_FN "verifier.assert"
#define VERIFIER_ASSERT_NOT_FN "verifier.assert.not"
#define VERIFIER_SYNTH_ASSUME_FN "sea.synth.assume"
#define VERIFIER_SYNTH_ASSERT_FN "sea.synth.assert"
#define SEA_IS_DEREFERENCEABLE "sea.is_dereferenceable"
#define SEA_ASSERT_IF "sea.assert.if"
#define SEA_BRANCH_SENTINEL "sea.branch_sentinel"
#define SEA_IS_MODIFIED "sea.is_modified"
#define SEA_RESET_MODIFIED "sea.reset_modified"
#define SEA_IS_READ "sea.is_read"
#define SEA_RESET_READ "sea.reset_read"
#define SEA_IS_ALLOC "sea.is_alloc"
#define SEA_TRACKING_ON "sea.tracking_on"
#define SEA_TRACKING_OFF "sea.tracking_off"
#define SEA_FREE "sea.free"
#define SEA_SET_SHADOWMEM "sea.set_shadowmem"
#define SEA_GET_SHADOWMEM "sea.get_shadowmem"
#define HYPER_PRE_GREATER "hyper.pre.gt"
#define HYPER_POST_GREATER "hyper.post.gt"

SeaBuiltinsOp
seahorn::SeaBuiltinsInfo::getSeaBuiltinOp(const llvm::CallBase &cb) const {
  using SBIOp = SeaBuiltinsOp;
  auto *F = cb.getCalledFunction();
  if (!F)
    return SBIOp::UNKNOWN;

  return StringSwitch<SBIOp>(F->getName())
      .Case(VERIFIER_ERROR_FN, SBIOp::ERROR)
      .Case(SEAHORN_FAIL_FN, SBIOp::FAIL)
      .Case(VERIFIER_ASSUME_FN, SBIOp::ASSUME)
      .Case(VERIFIER_ASSUME_NOT_FN, SBIOp::ASSUME_NOT)
      .Case(SEA_IS_DEREFERENCEABLE, SBIOp::IS_DEREFERENCEABLE)
      .Case(SEA_ASSERT_IF, SBIOp::ASSERT_IF)
      .Case(VERIFIER_ASSERT_FN, SBIOp::ASSERT)
      .Case(VERIFIER_ASSERT_NOT_FN, SBIOp::ASSERT_NOT)
      .Case(VERIFIER_SYNTH_ASSUME_FN, SBIOp::SYNTH_ASSUME)
      .Case(VERIFIER_SYNTH_ASSERT_FN, SBIOp::SYNTH_ASSERT)
      .Case(SEA_BRANCH_SENTINEL, SBIOp::BRANCH_SENTINEL)
      .Case(SEA_IS_MODIFIED, SBIOp::IS_MODIFIED)
      .Case(SEA_RESET_MODIFIED, SBIOp::RESET_MODIFIED)
      .Case(SEA_IS_READ, SBIOp::IS_READ)
      .Case(SEA_RESET_READ, SBIOp::RESET_READ)
      .Case(SEA_IS_ALLOC, SBIOp::IS_ALLOC)
      .Case(SEA_TRACKING_ON, SBIOp::TRACKING_ON)
      .Case(SEA_TRACKING_OFF, SBIOp::TRACKING_OFF)
      .Case(SEA_FREE, SBIOp::FREE)
      .Case(SEA_SET_SHADOWMEM, SBIOp::SET_SHADOWMEM)
      .Case(SEA_GET_SHADOWMEM, SBIOp::GET_SHADOWMEM)
      .Case(HYPER_PRE_GREATER, SBIOp::HYPER_PRE_GT)
      .Case(HYPER_POST_GREATER, SBIOp::HYPER_POST_GT)
      .Default(SBIOp::UNKNOWN);
}

llvm::Function *SeaBuiltinsInfo::mkSeaBuiltinFn(SeaBuiltinsOp op,
                                                llvm::Module &M) {
  using SBIOp = SeaBuiltinsOp;
  switch (op) {
  default:
    return nullptr;
  case SBIOp::ERROR:
    return mkErrorFn(M);
  case SBIOp::FAIL:
    return mkFailFn(M);
  case SBIOp::ASSUME:
  case SBIOp::ASSUME_NOT:
    return mkAssertAssumeFn(M, op);
  case SBIOp::IS_DEREFERENCEABLE:
    return mkIsDereferenceable(M);
  case SBIOp::ASSERT_IF:
    return mkAssertIfFn(M);
  case SBIOp::ASSERT:
  case SBIOp::ASSERT_NOT:
    return mkAssertFn(M, op);
  case SBIOp::SYNTH_ASSUME:
    return mkSynthAssume(M);
  case SBIOp::SYNTH_ASSERT:
    return mkSynthAssert(M);
  case SBIOp::BRANCH_SENTINEL:
    return mkBranchSentinelFn(M);
  case SBIOp::IS_MODIFIED:
    return mkIsModifiedFn(M);
  case SBIOp::RESET_MODIFIED:
    return mkResetModifiedFn(M);
  case SBIOp::IS_READ:
    return mkIsReadFn(M);
  case SBIOp::RESET_READ:
    return mkResetReadFn(M);
  case SBIOp::IS_ALLOC:
    return mkIsAllocFn(M);
  case SBIOp::TRACKING_ON:
    return mkTrackingOnFn(M);
  case SBIOp::TRACKING_OFF:
    return mkTrackingOffFn(M);
  case SBIOp::FREE:
    return mkFreeFn(M);
  case SBIOp::SET_SHADOWMEM:
    return mkSetShadowMem(M);
  case SBIOp::GET_SHADOWMEM:
    return mkGetShadowMem(M);
  case SBIOp::HYPER_PRE_GT:
  case SBIOp::HYPER_POST_GT:
    return mkHyper(M, op);
  }
  llvm_unreachable(nullptr);
}

void SeaBuiltinsInfo::setCommonAttrs(Function &F) {
  auto &C = F.getContext();
  AttrBuilder B(C);
  B.addAttribute(Attribute::NoUnwind);
  B.addAttribute(Attribute::NoRecurse);
  B.addAttribute(Attribute::NoFree);
  B.addAttribute(Attribute::InaccessibleMemOnly);

  AttributeList as = AttributeList::get(C, AttributeList::FunctionIndex, B);
  F.setAttributes(as);
}
Function *SeaBuiltinsInfo::mkErrorFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(VERIFIER_ERROR_FN, Type::getVoidTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    setCommonAttrs(*FN);
    FN->setDoesNotReturn();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkFailFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEAHORN_FAIL_FN, Type::getVoidTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    setCommonAttrs(*FN);
    // FN->setDoesNotReturn();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkAssertAssumeFn(Module &M, SeaBuiltinsOp op) {
  auto &C = M.getContext();
  const char *name = nullptr;
  using SBIOp = SeaBuiltinsOp;
  switch (op) {
  default:
    assert(false);
    llvm_unreachable(nullptr);
  case SBIOp::ASSUME:
    name = VERIFIER_ASSUME_FN;
    break;
  case SBIOp::ASSUME_NOT:
    name = VERIFIER_ASSUME_NOT_FN;
    break;
  }
  auto FC = M.getOrInsertFunction(name, Type::getVoidTy(C), Type::getInt1Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    setCommonAttrs(*FN);
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkIsModifiedFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_IS_MODIFIED, Type::getInt1Ty(C),
                                  Type::getInt8PtrTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyReadsMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(0, Attribute::NoCapture);
    // XXX maybe even add the following
    // FN->setDoesNotAccessMemory();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkResetModifiedFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_RESET_MODIFIED, Type::getVoidTy(C),
                                  Type::getInt8PtrTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(0, Attribute::NoCapture);
    // XXX maybe even add the following
    // FN->setDoesNotAccessMemory();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkIsReadFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_IS_READ, Type::getInt1Ty(C),
                                  Type::getInt8PtrTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyReadsMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(0, Attribute::NoCapture);
    // XXX maybe even add the following
    // FN->setDoesNotAccessMemory();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkResetReadFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_RESET_READ, Type::getVoidTy(C),
                                  Type::getInt8PtrTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(0, Attribute::NoCapture);
    // XXX maybe even add the following
    // FN->setDoesNotAccessMemory();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkGetShadowMem(llvm::Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_GET_SHADOWMEM,
                                  Type::getInt8Ty(C),   // return type
                                  Type::getInt8Ty(C),   // slot number 0..255
                                  Type::getInt8PtrTy(C) // address int8_t*
  );
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyReadsMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(1, Attribute::NoCapture);
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkSetShadowMem(llvm::Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_SET_SHADOWMEM,
                                  Type::getVoidTy(C),    // return type
                                  Type::getInt8Ty(C),    // slot number 0..255
                                  Type::getInt8PtrTy(C), // address int8_t*
                                  Type::getInt8Ty(C)     // value to set
  );
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(1, Attribute::NoCapture);
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkIsAllocFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_IS_ALLOC, Type::getInt1Ty(C),
                                  Type::getInt8PtrTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyReadsMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(0, Attribute::NoCapture);
    // XXX maybe even add the following
    // FN->setDoesNotAccessMemory();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkIsDereferenceable(Module &M) {
  auto &C = M.getContext();
  auto *IntPtrTy = M.getDataLayout().getIntPtrType(C);
  auto FC = M.getOrInsertFunction(SEA_IS_DEREFERENCEABLE, Type::getInt1Ty(C),
                                  Type::getInt8PtrTy(C), IntPtrTy);
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyAccessesInaccessibleMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
    FN->addParamAttr(0, Attribute::NoCapture);
    // XXX maybe even add the following
    // FN->setDoesNotAccessMemory();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkAssertIfFn(llvm::Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_ASSERT_IF, Type::getVoidTy(C),
                                  Type::getInt1Ty(C), Type::getInt1Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyAccessesInaccessibleMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkAssertFn(llvm::Module &M, SeaBuiltinsOp op) {
  const char *name = nullptr;
  switch (op) {
  default:
    assert(false);
    llvm_unreachable(nullptr);
  case SeaBuiltinsOp::ASSERT:
    name = VERIFIER_ASSERT_FN;
    break;
  case SeaBuiltinsOp::ASSERT_NOT:
    name = VERIFIER_ASSERT_NOT_FN;
    break;
  }
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(name, Type::getVoidTy(C), Type::getInt1Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyAccessesInaccessibleMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkSynthAssume(llvm::Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(VERIFIER_SYNTH_ASSUME_FN, Type::getVoidTy(C),
                                  Type::getInt1Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    setCommonAttrs(*FN);
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkSynthAssert(llvm::Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(VERIFIER_SYNTH_ASSERT_FN, Type::getVoidTy(C),
                                  Type::getInt1Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyAccessesInaccessibleMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkBranchSentinelFn(llvm::Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_BRANCH_SENTINEL, Type::getVoidTy(C),
                                  Type::getInt1Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setOnlyAccessesInaccessibleMemory();
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkTrackingOnFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_TRACKING_ON, Type::getVoidTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkTrackingOffFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_TRACKING_OFF, Type::getVoidTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setDoesNotThrow();
    FN->setDoesNotFreeMemory();
    FN->setDoesNotRecurse();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkFreeFn(Module &M) {
  auto &C = M.getContext();
  auto FC = M.getOrInsertFunction(SEA_FREE, Type::getVoidTy(C),
                                  Type::getInt8PtrTy(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    FN->setDoesNotThrow();
    FN->setDoesNotRecurse();
    // This only marks the memory as freed an does not have the semantics for
    // actually freeing memory.
    FN->setDoesNotFreeMemory();
    FN->addParamAttr(0, Attribute::NoCapture);
    // XXX maybe even add the following
    // FN->setDoesNotAccessMemory();
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkHyper(Module &M, SeaBuiltinsOp op) {
  auto &C = M.getContext();
  const char *name = nullptr;
  using SBIOp = SeaBuiltinsOp;
  switch (op) {
  default:
    assert(false);
    llvm_unreachable(nullptr);
  case SBIOp::HYPER_PRE_GT:
    name = HYPER_PRE_GREATER;
    break;
  case SBIOp::HYPER_POST_GT:
    name = HYPER_POST_GREATER;
    break;
  }
  auto FC = M.getOrInsertFunction(name, Type::getVoidTy(C), Type::getInt32Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    setCommonAttrs(*FN);
  }
  return FN;
}

SeaBuiltinsInfoWrapperPass::SeaBuiltinsInfoWrapperPass() : ImmutablePass(ID) {
  initializeSeaBuiltinsInfoWrapperPassPass(*PassRegistry::getPassRegistry());
}

char seahorn::SeaBuiltinsInfoWrapperPass::ID = 0;

llvm::ImmutablePass *seahorn::createSeaBuiltinsWrapperPass() {
  return new SeaBuiltinsInfoWrapperPass();
}

using namespace seahorn;
INITIALIZE_PASS(SeaBuiltinsInfoWrapperPass, "sea-builtins",
                "Information and construciton of builtin seahorn functions",
                false, true)
