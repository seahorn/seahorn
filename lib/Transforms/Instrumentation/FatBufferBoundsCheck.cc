/**
SeaHorn Verification Framework
Copyright (c) 2020 Arie Gurfinkel
All Rights Reserved.

Released under a modified BSD license, please see license.txt for full
terms.

Based on BufferBoundsCheck from LLVM project
*/

//===----------------------------------------------------------------------===//
//
// This file implements a pass that instruments the code to perform run-time
// bounds checking on loads, stores, and other memory intrinsics. Unlike the
// original version, it uses "fat" pointers to store additional meta information
// about memory being pointed
//
//===----------------------------------------------------------------------===//

#include "llvm/ADT/Statistic.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetFolder.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Intrinsics.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Instrumentation.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "seahorn/config.h"
using namespace llvm;

#define DEBUG_TYPE "sea-bounds-checking"

#ifdef FAT_USE_FP
#define SEA_SET_FAT_SLOT0 "__sea_set_extptr_slot0_fp"
#define SEA_GET_FAT_SLOT0 "__sea_get_extptr_slot0_fp"
#define SEA_SET_FAT_SLOT1 "__sea_set_extptr_slot1_fp"
#define SEA_GET_FAT_SLOT1 "__sea_get_extptr_slot1_fp"
#define SEA_COPY_FAT_SLOTS "__sea_copy_extptr_slots_fp"
#define SEA_RECOVER_FAT_PTR "__sea_recover_pointer_fp"
#else
#define SEA_SET_FAT_SLOT0 "__sea_set_extptr_slot0_hm"
#define SEA_GET_FAT_SLOT0 "__sea_get_extptr_slot0_hm"
#define SEA_SET_FAT_SLOT1 "__sea_set_extptr_slot1_hm"
#define SEA_GET_FAT_SLOT1 "__sea_get_extptr_slot1_hm"
#define SEA_COPY_FAT_SLOTS "__sea_copy_extptr_slots_hm"
#define SEA_RECOVER_FAT_PTR "__sea_recover_pointer_hm"
#endif

// static cl::opt<bool> SingleErrorBB("bounds-checking-single-trap",
//                                  cl::desc("Use one trap block per
//                                  function"));

STATISTIC(ChecksAdded, "Bounds checks added");
STATISTIC(ChecksSkipped, "Bounds checks skipped");
STATISTIC(ChecksUnable, "Bounds checks unable to add");

typedef IRBuilder<TargetFolder> BuilderTy;

namespace {
struct FatBufferBoundsCheck : public FunctionPass {
  static char ID;
  FatBufferBoundsCheck() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetLibraryInfoWrapperPass>();
  }

private:
  const TargetLibraryInfo *TLI;
  ObjectSizeOffsetEvaluator *ObjSizeEval;
  BuilderTy *Builder;
  Instruction *Inst;
  BasicBlock *ErrorBB;
  Type *IntptrTy;
  LLVMContext *Ctx;
  Module *Mod;
  Function *m_setFatSlot0;   // set ptr base
  Function *m_setFatSlot1;   // set ptr size
  Function *m_getFatSlot0;   // get ptr base
  Function *m_getFatSlot1;   // get ptr size
  Function *m_copyFatSlots;  // copy ptr info
  Function *m_recoverFatPtr; // NEW: for ptr embed method only
  Value *OrigPtr;

  BasicBlock *getErrorBB();
  void emitBranchToTrap(Value *Cmp = nullptr);
  bool instrument(Value *Ptr, Value *Val, const DataLayout &DL);
  bool instrumentAddress(Value *Ptr, const DataLayout &DL,
                         Value *BasePtr = nullptr);
  // Value* memToShadow(Value *mem, BuilderTy *builder);
};
} // namespace

char FatBufferBoundsCheck::ID = 0;

/// getErrorBB - create a basic block that traps. All overflowing conditions
/// branch to this block. There's only one trap block per function.
BasicBlock *FatBufferBoundsCheck::getErrorBB() {
  if (ErrorBB)
    return ErrorBB;

  Function *Fn = Inst->getParent()->getParent();
  Module *Md = Fn->getParent();
  LLVMContext &ctx = Md->getContext();
  IRBuilder<>::InsertPointGuard Guard(*Builder);
  ErrorBB = BasicBlock::Create(Fn->getContext(), "bound_overflow", Fn);
  Builder->SetInsertPoint(ErrorBB);

  AttrBuilder AB;
  AB.addAttribute(Attribute::NoReturn);
  AttributeList as = AttributeList::get(ctx, AttributeList::FunctionIndex, AB);
  // XXX use generic __VERIFIER_error() function to ensure that it is properly
  // XXX lifted to verifier.error() with PromoteVerifierCalls pass. A better
  // XXX solution is to unify how seahorn-specific functions are accessed to
  // XXX ensure that they are always created uniformly with the right
  // XXX attributes.
  auto errorFn = dyn_cast<Function>(
      Md->getOrInsertFunction("__VERIFIER_error", as, Type::getVoidTy(ctx)));
  CallInst *TrapCall = Builder->CreateCall(errorFn);
  TrapCall->setDoesNotReturn();
  TrapCall->setDoesNotThrow();
  TrapCall->setDebugLoc(Inst->getDebugLoc());
  Builder->CreateUnreachable();

  return ErrorBB;
}

/// emitBranchToTrap - emit a branch instruction to a trap block.
/// If Cmp is non-null, perform a jump only if its value evaluates to true.
void FatBufferBoundsCheck::emitBranchToTrap(Value *Cmp) {
  // check if the comparison is always false
  ConstantInt *C = dyn_cast_or_null<ConstantInt>(Cmp);
  if (C) {
    ++ChecksSkipped;
    if (!C->getZExtValue())
      return;
    else
      Cmp = nullptr; // unconditional branch
  }
  ++ChecksAdded;

  BasicBlock::iterator Inst = Builder->GetInsertPoint();
  BasicBlock *OldBB = Inst->getParent();
  BasicBlock *Cont = OldBB->splitBasicBlock(Inst);
  OldBB->getTerminator()->eraseFromParent();

  if (Cmp)
    BranchInst::Create(getErrorBB(), Cont, Cmp, OldBB);
  else
    BranchInst::Create(getErrorBB(), OldBB);
}

/// instrument - adds run-time bounds checks to memory accessing instructions.
/// Ptr is the pointer that will be read/written, and InstVal is either the
/// result from the load or the value being stored. It is used to determine the
/// size of memory block that is touched.
/// Returns true if any change was made to the IR, false otherwise.
bool FatBufferBoundsCheck::instrument(Value *Ptr, Value *InstVal,
                                      const DataLayout &DL) {
  uint64_t NeededSize = DL.getTypeStoreSize(InstVal->getType());
  Value *NeededSizeVal = ConstantInt::get(IntptrTy, NeededSize);
  LOG("fat-bnd-check", errs() << "Instrument " << *Ptr << " for "
                              << Twine(NeededSize) << " bytes\n");
  SizeOffsetEvalType SizeOffset = ObjSizeEval->compute(Ptr);
  Value *Or;

  if (!ObjSizeEval->bothKnown(SizeOffset)) {
    LOG("fat-bnd-check", errs() << "fatptr instrument " << *Ptr << " for "
                                << Twine(NeededSize) << " bytes\n";);
    /* Generates code for dynamic bounds check using fat ptr functions:
      start := call get_fat_slot0(ptr)
      size  := call get_fat_slot1(ptr)
      (optionally, for fat encoding implementation)
      recov := call recover_fatptr(ptr)
      is_underflow := (ptr < start) ptr_end = start + size
      access_end := ptr + needed_size
      is_overflow := ptr_end < access_end
      is_access_bad := is_underflow or is_overflow
    */
    // get start and end by calling internalized functions
    Value *Start = Builder->CreateCall(
        m_getFatSlot0, Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
    Value *Size = Builder->CreateCall(
        m_getFatSlot1, Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
    Value *recov = Builder->CreateCall(
        m_recoverFatPtr, Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
    OrigPtr = Builder->CreateBitCast(recov, Ptr->getType());
    Value *PtrInt = Builder->CreatePtrToInt(OrigPtr, IntptrTy);
    // Ptr >= Start
    Value *CmpUnderFlow = Builder->CreateICmpULT(
        PtrInt, Builder->CreateIntCast(Start, IntptrTy, true));
    // Start + Size >= Ptr + NeededSize
    Value *accessEnd = Builder->CreateAdd(PtrInt, NeededSizeVal);
    Value *ptrEnd = Builder->CreateAdd(Start, Size);
    Value *CmpOverFlow = Builder->CreateICmpULT(
        Builder->CreateIntCast(ptrEnd, IntptrTy, true), accessEnd);
    Or = Builder->CreateOr(CmpUnderFlow, CmpOverFlow);
  } else {
    // size and offest statically computed
    LOG("fat-bnd-check", errs() << "statically instrument " << *Ptr << " for "
                                << Twine(NeededSize) << " bytes\n";);
    Value *Size = SizeOffset.first;
    Value *Offset = SizeOffset.second;
    ConstantInt *SizeCI = dyn_cast<ConstantInt>(Size);

    // three checks are required to ensure safety:
    // . Offset >= 0  (since the offset is given from the base ptr)
    // . Size >= Offset  (unsigned)
    // . Size - Offset >= NeededSize  (unsigned)
    //
    // optimization: if Size >= 0 (signed), skip 1st check
    // FIXME: add NSW/NUW here?  -- we dont care if the subtraction overflows
    Value *ObjSize = Builder->CreateSub(Size, Offset);
    Value *Cmp2 = Builder->CreateICmpULT(Size, Offset);
    Value *Cmp3 = Builder->CreateICmpULT(ObjSize, NeededSizeVal);
    Or = Builder->CreateOr(Cmp2, Cmp3);
    if (!SizeCI || SizeCI->getValue().slt(0)) {
      Value *Cmp1 =
          Builder->CreateICmpSLT(Offset, ConstantInt::get(IntptrTy, 0));
      Or = Builder->CreateOr(Cmp1, Or);
    }
    OrigPtr = Ptr;
  }
  emitBranchToTrap(Or);

  return true;
}

/* Record information of address Ptr, store/update the base address and size */
bool FatBufferBoundsCheck::instrumentAddress(Value *Ptr, const DataLayout &DL,
                                             Value *BasePtr) {
  /**
     Rewrite pointer creation to embed base address and size in the extended part of the pointer.

     This is a little tricky because need to ensure that the extended pointer
     replaces the original pointer in all the existing code, but not in the
     newly generated code.

     The solution is to create new code with a placeholder for where the old
     pointer goes. Replaces old pointer by new everywhere. Then plug the old
     pointer into the placeholder left for it.
   */
  Ptr->setName("raw_ptr");
  Type *resultType;
  /* BasePtr not provided: processing store instructions
    with_base := call set_fat_slot0(ptr)
    with_size_and_base := call set_fat_slot1(with_base)
    replace_all(ptr, with_size_and_base)
  */
  if (!BasePtr) {
    if (auto *ALI = dyn_cast<AllocaInst>(Ptr)) {
      resultType = ALI->getAllocatedType();
    } else {
      ERR << "Unexpected instruction: " << *Ptr << "\n";
      assert(false && "Unexpected instruction");
    }
    CallInst *withBase = Builder->CreateCall(
        m_setFatSlot0, {Constant::getNullValue(Builder->getInt8PtrTy()),
                        ConstantInt::get(IntptrTy, 0)});
    // set_fat_slot1(Ptr, Size)
    CallInst *withSize = Builder->CreateCall(
        m_setFatSlot1, {Constant::getNullValue(Builder->getInt8PtrTy()),
                        ConstantInt::get(IntptrTy, 0)});
    Value *casted =
        Builder->CreateBitCast(withSize, resultType->getPointerTo());
    Ptr->replaceAllUsesWith(casted);
    Value *sizeVal;
    // alloca
    if (auto *ALI = dyn_cast<AllocaInst>(Ptr)) {
      uint64_t size = DL.getTypeStoreSize(ALI->getAllocatedType());
      sizeVal = ConstantInt::get(IntptrTy, size);
    } else {
      ERR << "Could not determine base address: " << *Ptr;
      assert(false && "unexpected lack of base address");
    }
    // set_fat_slot0(Ptr, Base)
    Builder->SetInsertPoint(withBase);
    Value *argA = Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy());
    Value *argB = Builder->CreatePtrToInt(Ptr, IntptrTy);
    withBase->setArgOperand(0, argA);
    withBase->setArgOperand(1, argB);
    Builder->SetInsertPoint(withSize);
    argA = Builder->CreateBitCast(withBase, Builder->getInt8PtrTy());
    withSize->setArgOperand(0, argA);
    withSize->setArgOperand(1, sizeVal);
  } else {
    /* Additional BasePtr is provided: processing GEP
      copied := call copy_fat_slots(ptr, base_ptr)
      replace_all(ptr, copied)
    */
    // copy_fat_slots(Ptr, BasePtr)
    if (auto *GEP = dyn_cast<GetElementPtrInst>(Ptr)) {
      resultType = GEP->getResultElementType();
    } else {
      ERR << "Unexpected non-gep instruction: " << *Ptr << "\n";
      assert(false && "only handling GEP instructions");
    }
    CallInst *copied = Builder->CreateCall(
        m_copyFatSlots, {Constant::getNullValue(Builder->getInt8PtrTy()),
                         Constant::getNullValue(Builder->getInt8PtrTy())});
    Value *casted = Builder->CreateBitCast(copied, resultType->getPointerTo());
    LOG("fat-bnd-check", errs() << "casting  " << *Ptr << " to " << *casted
                                << " with type " << *resultType->getPointerTo()
                                << " \n";);
    Ptr->replaceAllUsesWith(casted);
    Builder->SetInsertPoint(copied);
    copied->setArgOperand(0,
                          Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
    copied->setArgOperand(
        1, Builder->CreateBitCast(BasePtr, Builder->getInt8PtrTy()));
  }

  return true;
}

bool FatBufferBoundsCheck::runOnFunction(Function &F) {
  Mod = F.getParent();
  const DataLayout &DL = F.getParent()->getDataLayout();
  TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();

  ErrorBB = nullptr;
  BuilderTy TheBuilder(F.getContext(), TargetFolder(DL));
  Builder = &TheBuilder;
  ObjectSizeOffsetEvaluator TheObjSizeEval(DL, TLI, F.getContext(),
                                           /*RoundToAlign=*/true);
  ObjSizeEval = &TheObjSizeEval;

  Ctx = &(F.getContext());
  int LongSize = DL.getPointerSizeInBits();
  IntptrTy = Type::getIntNTy(F.getContext(), LongSize);

  m_getFatSlot0 = cast<Function>(Mod->getOrInsertFunction(
      SEA_GET_FAT_SLOT0, IntptrTy, Type::getInt8PtrTy(*Ctx, 0)));
  m_getFatSlot1 = cast<Function>(Mod->getOrInsertFunction(
      SEA_GET_FAT_SLOT1, IntptrTy, Type::getInt8PtrTy(*Ctx, 0)));

  m_setFatSlot0 = cast<Function>(
      Mod->getOrInsertFunction(SEA_SET_FAT_SLOT0, Type::getInt8PtrTy(*Ctx, 0),
                               Type::getInt8PtrTy(*Ctx, 0), IntptrTy));
  m_setFatSlot1 = cast<Function>(
      Mod->getOrInsertFunction(SEA_SET_FAT_SLOT1, Type::getInt8PtrTy(*Ctx, 0),
                               Type::getInt8PtrTy(*Ctx, 0), IntptrTy));

  m_copyFatSlots = cast<Function>(Mod->getOrInsertFunction(
      SEA_COPY_FAT_SLOTS, Type::getInt8PtrTy(*Ctx, 0),
      Type::getInt8PtrTy(*Ctx, 0), Type::getInt8PtrTy(*Ctx, 0)));

  m_recoverFatPtr = cast<Function>(
      Mod->getOrInsertFunction(SEA_RECOVER_FAT_PTR, Type::getInt8PtrTy(*Ctx, 0),
                               Type::getInt8PtrTy(*Ctx, 0)));

  // check HANDLE_MEMORY_INST in include/llvm/Instruction.def for memory
  // touching instructions
  std::vector<Instruction *> AccessWorkList;
  std::vector<Instruction *> AllocaList; // new register is created for addr
  std::vector<Instruction *> GEPList;    // new register is created for addr
  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;
    if (isa<LoadInst>(I) || isa<StoreInst>(I) || isa<AtomicCmpXchgInst>(I) ||
        isa<AtomicRMWInst>(I)) {
      AccessWorkList.push_back(I);
      continue;
    }
    if (isa<AllocaInst>(I)) {
      AllocaList.push_back(I);
    }
    if (isa<GetElementPtrInst>(I)) {
      GEPList.push_back(I);
    }
  }

  bool MadeChange = false;
  for (Instruction *i : AllocaList) {
    Inst = i;
    Builder->SetInsertPoint(Inst->getNextNode()); // insert after
    if (AllocaInst *ALI = dyn_cast<AllocaInst>(Inst)) {
      Type *allocTy = ALI->getAllocatedType();
      if (allocTy->isArrayTy() || allocTy->isPointerTy() ||
          allocTy->isStructTy()) {
        MadeChange |= instrumentAddress(ALI, DL);
      }
    } else {
      llvm_unreachable("unknown Instruction type");
    }
  }

  for (Instruction *i : GEPList) {
    Inst = i;
    Builder->SetInsertPoint(Inst->getNextNode()); // insert after
    if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Inst)) {
      MadeChange |= instrumentAddress(GEP, DL, GEP->getPointerOperand());
    } else {
      llvm_unreachable("unknown Instruction type");
    }
  }

  for (Instruction *i : AccessWorkList) {
    Inst = i;

    Builder->SetInsertPoint(Inst);
    if (LoadInst *LI = dyn_cast<LoadInst>(Inst)) {
      MadeChange |= instrument(LI->getPointerOperand(), LI, DL);
      LI->setOperand(LI->getPointerOperandIndex(), OrigPtr);
    } else if (StoreInst *SI = dyn_cast<StoreInst>(Inst)) {
      MadeChange |=
          instrument(SI->getPointerOperand(), SI->getValueOperand(), DL);
      SI->setOperand(SI->getPointerOperandIndex(), OrigPtr);
    } else if (AtomicCmpXchgInst *AI = dyn_cast<AtomicCmpXchgInst>(Inst)) {
      MadeChange |=
          instrument(AI->getPointerOperand(), AI->getCompareOperand(), DL);
      AI->setOperand(AI->getPointerOperandIndex(), OrigPtr);
    } else if (AtomicRMWInst *AI = dyn_cast<AtomicRMWInst>(Inst)) {
      MadeChange |=
          instrument(AI->getPointerOperand(), AI->getValOperand(), DL);
      AI->setOperand(AI->getPointerOperandIndex(), OrigPtr);
    } else {
      llvm_unreachable("unknown Instruction type");
    }
  }
  return MadeChange;
}
namespace seahorn {
FunctionPass *createFatBufferBoundsCheckPass() {
  return new FatBufferBoundsCheck();
}
} // namespace seahorn

static RegisterPass<FatBufferBoundsCheck>
    X("fat-buffer-bounds-instrument",
      "Bounds checking based on extended pointer");
