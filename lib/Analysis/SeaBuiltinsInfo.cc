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
#define SEA_IS_DEREFERENCEABLE "sea.is_dereferenceable"

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
  }
  llvm_unreachable(nullptr);
}

void SeaBuiltinsInfo::setCommonAttrs(Function &F) {
  auto &C = F.getContext();
  AttrBuilder B;
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
  char *name = nullptr;
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
  case SBIOp::ASSERT:
    name = VERIFIER_ASSERT_FN;
    break;
  case SBIOp::ASSERT_NOT:
    name = VERIFIER_ASSERT_NOT_FN;
    break;
  }
  auto FC = M.getOrInsertFunction(name, Type::getVoidTy(C), Type::getInt1Ty(C));
  auto *FN = dyn_cast<Function>(FC.getCallee());
  if (FN) {
    setCommonAttrs(*FN);
  }
  return FN;
}

Function *SeaBuiltinsInfo::mkIsDereferenceable(Module &M) {
  auto &C = M.getContext();
  auto *IntPtrTy = M.getDataLayout().getIntPtrType(C);
  auto FC = M.getOrInsertFunction(SEA_IS_DEREFERENCEABLE, Type::getInt1Ty(C), Type::getInt8PtrTy(C), IntPtrTy);
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

SeaBuiltinsInfoWrapperPass::SeaBuiltinsInfoWrapperPass() : ImmutablePass(ID) {
  initializeSeaBuiltinsInfoWrapperPassPass(*PassRegistry::getPassRegistry());
}

char seahorn::SeaBuiltinsInfoWrapperPass::ID = 0;

llvm::ImmutablePass *seahorn::createSeaBuiltinsWrapperPass() {
  return new SeaBuiltinsInfoWrapperPass();
}

namespace llvm {
using namespace seahorn;
INITIALIZE_PASS(SeaBuiltinsInfoWrapperPass, "sea-builtins",
                "Information and construciton of builtin seahorn functions",
                false, true)
} // namespace llvm
