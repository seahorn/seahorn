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

#include "seahorn/InitializePasses.hh"

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

#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "seahorn/config.h"
using namespace llvm;

static llvm::cl::list<std::string> NoInstrumentFunctionNames(
    "no-bound-check-fns",
    llvm::cl::desc("Functions for which to skip bound check"),
    llvm::cl::ZeroOrMore, llvm::cl::CommaSeparated);

#define DEBUG_TYPE "sea-bounds-checking"

#define SEA_DSA_ALIAS "sea_dsa_alias"
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

static cl::opt<bool>
    UseFatSlots("horn-bnd-chk-slots",
                cl::desc("Use instrumentation based on fat slots"),
                cl::init(true));

STATISTIC(ChecksAdded, "Bounds checks added");
STATISTIC(ChecksSkipped, "Bounds checks skipped");
STATISTIC(ChecksUnable, "Bounds checks unable to add");
STATISTIC(ChecksFat, "Bounds checks that use fat pointers");
STATISTIC(ChecksKnownSize, "Bounds checks that have known size but not offset");

typedef IRBuilder<TargetFolder> BuilderTy;

namespace {
struct FatBufferBoundsCheck : public FunctionPass {
  static char ID;
  FatBufferBoundsCheck() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.addRequired<TargetLibraryInfoWrapperPass>();
    AU.addRequired<seahorn::SeaBuiltinsInfoWrapperPass>();
  }

private:
  const TargetLibraryInfo *TLI;
  seahorn::SeaBuiltinsInfo *SBI;
  ObjectSizeOffsetEvaluator *ObjSizeEval;
  BuilderTy *Builder;
  Instruction *Inst;
  BasicBlock *ErrorBB;
  Type *IntPtrTy;
  Function *m_setFatSlot0;   // set ptr base
  Function *m_setFatSlot1;   // set ptr size
  Function *m_getFatSlot0;   // get ptr base
  Function *m_getFatSlot1;   // get ptr size
  Function *m_copyFatSlots;  // copy ptr info
  Function *m_recoverFatPtr; // NEW: for ptr embed method only
  Function *m_seaDsaAlias;   // sea_dsa_alias

  Function *m_seaIsDereferenceable; // sea.is_dereferenceable

  BasicBlock *getErrorBB();
  void emitBranchToTrap(Value *Cmp = nullptr);
  bool instrument(Value *Ptr, Value *Val, const DataLayout &DL, Value *&RawPtr);
  bool instrumentAlloca(AllocaInst *Ptr, const DataLayout &DL);
  bool instrumentGep(GetElementPtrInst *Ptr, Value *&RawPtr);
};
} // namespace

char FatBufferBoundsCheck::ID = 0;

/// getErrorBB - create a basic block that traps. All overflowing conditions
/// branch to this block. There's only one trap block per function.
BasicBlock *FatBufferBoundsCheck::getErrorBB() {
  if (ErrorBB)
    return ErrorBB;

  Function *Fn = Inst->getParent()->getParent();
  Module &M = *Fn->getParent();
  LLVMContext &ctx = M.getContext();
  IRBuilder<>::InsertPointGuard Guard(*Builder);
  ErrorBB = BasicBlock::Create(Fn->getContext(), "bound_overflow", Fn);
  Builder->SetInsertPoint(ErrorBB);

  AttrBuilder AB;
  AB.addAttribute(Attribute::NoReturn);
  AttributeList as = AttributeList::get(ctx, AttributeList::FunctionIndex, AB);
  auto errorFn = SBI->mkSeaBuiltinFn(seahorn::SeaBuiltinsOp::ERROR, M);
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
                                      const DataLayout &DL, Value *&RawPtr) {
  uint64_t NeededSize = DL.getTypeStoreSize(InstVal->getType());
  Value *NeededSizeVal = ConstantInt::get(IntPtrTy, NeededSize);
  LOG("fat-bnd-check", errs() << "Instrument " << *Ptr << " for "
                              << Twine(NeededSize) << " bytes\n");
  SizeOffsetEvalType SizeOffset = ObjSizeEval->compute(Ptr);
  Value *Or;

  if (UseFatSlots) {
    auto *ArgPtr = Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy());
    Value *RecovPtr = Builder->CreateCall(m_recoverFatPtr, ArgPtr);
    RawPtr = Builder->CreateBitCast(RecovPtr, Ptr->getType());
    Builder->CreateCall(m_seaDsaAlias, {ArgPtr, RecovPtr});
  } else {
    RawPtr = Ptr;
  }

  if (!ObjSizeEval->bothKnown(SizeOffset)) {
    if (auto *GV = dyn_cast<GlobalVariable>(Ptr)) {
      // stderr is usually external and ObjSizeEval refuses to determine its
      // size
      if (GV->getName().equals("stderr")) {
        LOG("fat-bnd-check", errs() << "not instrumenting access to stderr\n";);
        return false;
      }
    }
    if (UseFatSlots) {
      // -- skip anything that is globally allocated
      if (isa<llvm::GlobalValue>(Ptr->stripPointerCastsAndInvariantGroups())) {
        ++ChecksUnable;
        return false;
      }

      ++ChecksFat;
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
      Value *Start = Builder->CreateCall(
          m_getFatSlot0, Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
      Value *Size = nullptr;
      if (ObjSizeEval->knownSize(SizeOffset)) {
        Size = SizeOffset.first;
        ++ChecksKnownSize;
      } else {
        Size = Builder->CreateCall(
            m_getFatSlot1,
            Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
      }
      assert(Size);
      Value *PtrAsInt = Builder->CreatePtrToInt(RawPtr, IntPtrTy);
      // Ptr >= Start
      Value *CmpUnderFlow = Builder->CreateICmpULT(PtrAsInt, Start);
      // Start + Size >= Ptr + NeededSize
      Value *AccessEnd = Builder->CreateAdd(PtrAsInt, NeededSizeVal);
      Value *PtrEnd = Builder->CreateAdd(Start, Size);
      Value *CmpOverFlow = Builder->CreateICmpULT(PtrEnd, AccessEnd);
      Or = Builder->CreateOr(CmpUnderFlow, CmpOverFlow);
    } else {
      ++ChecksFat;
      LOG("fat-bnd-check", errs() << "fatptr instrument " << *Ptr << " for "
                                  << Twine(NeededSize) << " bytes\n";);
      auto isDerefCall = Builder->CreateCall(
          m_seaIsDereferenceable,
          {Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()),
           NeededSizeVal});
      Or = Builder->CreateNot(isDerefCall);
    }
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
          Builder->CreateICmpSLT(Offset, ConstantInt::get(IntPtrTy, 0));
      Or = Builder->CreateOr(Cmp1, Or);
    }
  }
  emitBranchToTrap(Or);

  return true;
}

bool FatBufferBoundsCheck::instrumentAlloca(AllocaInst *Ptr,
                                            const DataLayout &DL) {
  /**
     Rewrite pointer creation to embed base address and size in the extended
     part of the pointer.

     This is a little tricky because need to ensure that the extended pointer
     replaces the original pointer in all the existing code, but not in the
     newly generated code.

     The solution is to create new code with a placeholder for where the old
     pointer goes. Replaces old pointer by new everywhere. Then plug the old
     pointer into the placeholder left for it.
   */
  auto *AllocedTy = Ptr->getAllocatedType();
  /* BasePtr not provided: processing store instructions
    with_base := call set_fat_slot0(ptr)
    with_size_and_base := call set_fat_slot1(with_base)
    replace_all(ptr, with_size_and_base)
  */

  Builder->SetInsertPoint(Ptr->getParent(), ++BasicBlock::iterator(Ptr));
  // -- forward created calls. Arguments will be filled later
  // -- create a call to set slot0
  CallInst *withBase = Builder->CreateCall(
      m_setFatSlot0, {Constant::getNullValue(Builder->getInt8PtrTy()),
                      ConstantInt::get(IntPtrTy, 0)});
  // -- create a call to set slot1
  CallInst *withSize = Builder->CreateCall(
      m_setFatSlot1, {Constant::getNullValue(Builder->getInt8PtrTy()),
                      ConstantInt::get(IntPtrTy, 0)});
  // -- cast result of setting slot1 to same type as returned by alloca
  Value *NewPtr = Builder->CreateBitCast(withSize, AllocedTy->getPointerTo());
  // -- replace all uses of the pointer with fat pointer
  // -- later pass will ensure that the pointer is recovered if it is used to
  // access memory
  Ptr->replaceAllUsesWith(NewPtr);

  // set_fat_slot0(Ptr, Base)
  Builder->SetInsertPoint(withBase);
  Value *argA = Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy());
  Value *argB = Builder->CreatePtrToInt(Ptr, IntPtrTy);
  withBase->setArgOperand(0, argA);
  withBase->setArgOperand(1, argB);

  // set_fat_slot1(Ptr, Size)
  auto argC = Builder->CreateBitCast(withBase, Builder->getInt8PtrTy());
  withSize->setArgOperand(0, argC);
  Builder->SetInsertPoint(withSize);
  auto size = DL.getTypeStoreSize(AllocedTy);
  auto *sizeVal = ConstantInt::get(IntPtrTy, size);
  withSize->setArgOperand(1, sizeVal);

  Builder->SetInsertPoint(withSize->getParent(),
                          ++BasicBlock::iterator(withSize));
  Builder->CreateCall(m_seaDsaAlias, {argA, argC});
  Builder->CreateCall(
      m_seaDsaAlias,
      {argC, Builder->CreateBitCast(withSize, Builder->getInt8PtrTy())});

  return true;
}

bool FatBufferBoundsCheck::instrumentGep(GetElementPtrInst *Ptr,
                                         Value *&RawPtr) {
  /*
    Transformation:
     copied := call copy_fat_slots(ptr, base_ptr)
     replace_all(ptr, copied)
 */
  // copy_fat_slots(Ptr, BasePtr)
  auto GepTy = Ptr->getResultElementType();
  auto *BasePtr = Ptr->getPointerOperand();

  Builder->SetInsertPoint(Ptr);
  auto *ArgBasePtr = Builder->CreateBitCast(BasePtr, Builder->getInt8PtrTy());
  Value *RecovPtr = Builder->CreateCall(m_recoverFatPtr, ArgBasePtr);

  Builder->CreateCall(m_seaDsaAlias, {ArgBasePtr, RecovPtr});
  RawPtr = Builder->CreateBitCast(RecovPtr, BasePtr->getType());

  Builder->SetInsertPoint(Ptr->getParent(), ++BasicBlock::iterator(Ptr));
  CallInst *SlotCopyCall = Builder->CreateCall(
      m_copyFatSlots, {Constant::getNullValue(Builder->getInt8PtrTy()),
                       Constant::getNullValue(Builder->getInt8PtrTy())});
  Value *Casted = Builder->CreateBitCast(SlotCopyCall, GepTy->getPointerTo());
  Ptr->replaceAllUsesWith(Casted);
  LOG("fat-bnd-check", errs()
                           << "casting  " << *Ptr << " to " << *Casted
                           << " with type " << *GepTy->getPointerTo() << "\n";);

  Builder->SetInsertPoint(SlotCopyCall);
  auto *Arg0 = Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy());
  auto *Arg1 = Builder->CreateBitCast(BasePtr, Builder->getInt8PtrTy());
  SlotCopyCall->setArgOperand(0, Arg0);
  SlotCopyCall->setArgOperand(1, Arg1);

  Builder->SetInsertPoint(Ptr->getParent(),
                          ++BasicBlock::iterator(SlotCopyCall));
  Builder->CreateCall(m_seaDsaAlias, {Arg0, SlotCopyCall});
  return true;
}

bool FatBufferBoundsCheck::runOnFunction(Function &F) {
  if (std::find(std::begin(NoInstrumentFunctionNames),
                std::end(NoInstrumentFunctionNames),
                F.getName()) != std::end(NoInstrumentFunctionNames)) {
    DOG(INFO << "skipping instrumentation of " << F.getName(););
    return false;
  }

  auto *M = F.getParent();
  auto &C = F.getContext();

  const auto &DL = M->getDataLayout();
  TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
  SBI = &getAnalysis<seahorn::SeaBuiltinsInfoWrapperPass>().getSBI();

  ErrorBB = nullptr;
  BuilderTy TheBuilder(F.getContext(), TargetFolder(DL));
  Builder = &TheBuilder;
  ObjectSizeOpts EvalOpts;
  EvalOpts.RoundToAlign = true;
  ObjectSizeOffsetEvaluator TheObjSizeEval(DL, TLI, F.getContext(), EvalOpts);
  ObjSizeEval = &TheObjSizeEval;

  IntPtrTy = DL.getIntPtrType(C);

  m_seaIsDereferenceable =
      SBI->mkSeaBuiltinFn(seahorn::SeaBuiltinsOp::IS_DEREFERENCEABLE, *M);

  if (UseFatSlots) {
    m_getFatSlot0 =
        cast<Function>(M->getOrInsertFunction(SEA_GET_FAT_SLOT0, IntPtrTy,
                                              Type::getInt8PtrTy(C, 0))
                           .getCallee());

    m_getFatSlot0->setDoesNotThrow();
    m_getFatSlot0->setDoesNotReadMemory();
    m_getFatSlot0->addParamAttr(0, Attribute::NoCapture);

    m_getFatSlot1 =
        cast<Function>(M->getOrInsertFunction(SEA_GET_FAT_SLOT1, IntPtrTy,
                                              Type::getInt8PtrTy(C, 0))
                           .getCallee());
    m_getFatSlot1->setDoesNotThrow();
    m_getFatSlot1->setDoesNotReadMemory();
    m_getFatSlot1->addParamAttr(0, Attribute::NoCapture);

    m_setFatSlot0 = cast<Function>(
        M->getOrInsertFunction(SEA_SET_FAT_SLOT0, Type::getInt8PtrTy(C, 0),
                               Type::getInt8PtrTy(C, 0), IntPtrTy)
            .getCallee());
    m_setFatSlot0->setDoesNotThrow();
    m_setFatSlot0->setDoesNotReadMemory();
    // m_setFatSlot0->addParamAttr(0, Attribute::Returned);

    m_setFatSlot1 = cast<Function>(
        M->getOrInsertFunction(SEA_SET_FAT_SLOT1, Type::getInt8PtrTy(C, 0),
                               Type::getInt8PtrTy(C, 0), IntPtrTy)
            .getCallee());
    m_setFatSlot1->setDoesNotThrow();
    m_setFatSlot1->setDoesNotReadMemory();
    // m_setFatSlot1->addParamAttr(0, Attribute::Returned);

    m_copyFatSlots =
        cast<Function>(M->getOrInsertFunction(
                            SEA_COPY_FAT_SLOTS, Type::getInt8PtrTy(C, 0),
                            Type::getInt8PtrTy(C, 0), Type::getInt8PtrTy(C, 0))
                           .getCallee());
    m_copyFatSlots->setDoesNotThrow();
    m_copyFatSlots->setDoesNotReadMemory();
    // m_copyFatSlots->addParamAttr(0, Attribute::Returned);
    m_copyFatSlots->addParamAttr(1, Attribute::NoCapture);

    m_recoverFatPtr = cast<Function>(
        M->getOrInsertFunction(SEA_RECOVER_FAT_PTR, Type::getInt8PtrTy(C, 0),
                               Type::getInt8PtrTy(C, 0))
            .getCallee());
    m_recoverFatPtr->setDoesNotThrow();
    m_recoverFatPtr->setDoesNotReadMemory();
    // m_recoverFatPtr->addParamAttr(0, Attribute::Returned);

    m_seaDsaAlias =
        cast<Function>(M->getOrInsertFunction(SEA_DSA_ALIAS, Type::getVoidTy(C),
                                              Type::getInt8PtrTy(C, 0),
                                              Type::getInt8PtrTy(C, 0))
                           .getCallee());
  }

  // check HANDLE_MEMORY_INST in include/llvm/Instruction.def for memory
  // touching instructions

  std::vector<AllocaInst *> AllocaList;     // new register is created for addr
  std::vector<GetElementPtrInst *> GEPList; // new register is created for addr
  std::vector<Instruction *> AccessWorkList;
  for (auto i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;
    if (isa<LoadInst>(I) || isa<StoreInst>(I) || isa<AtomicCmpXchgInst>(I) ||
        isa<AtomicRMWInst>(I)) {
      AccessWorkList.push_back(I);
    } else if (false && isa<AllocaInst>(I)) {
      AllocaList.push_back(cast<AllocaInst>(I));
    } else if (false && isa<GetElementPtrInst>(I)) {
      GEPList.push_back(cast<GetElementPtrInst>(I));
    }
  }

  bool MadeChange = false;
  if (UseFatSlots) {
    for (Instruction *i : AllocaList) {
      Inst = i;
      if (AllocaInst *ALI = dyn_cast<AllocaInst>(Inst)) {
        Type *allocTy = ALI->getAllocatedType();
        MadeChange |= instrumentAlloca(ALI, DL);
      } else {
        llvm_unreachable("unknown Instruction type");
      }
    }

    for (Instruction *i : GEPList) {
      Value *RawPtr = nullptr;
      Inst = i;
      if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Inst)) {
        MadeChange |= instrumentGep(GEP, RawPtr);
        GEP->setOperand(GEP->getPointerOperandIndex(), RawPtr);
      } else {
        llvm_unreachable("unknown Instruction type");
      }
    }
  }

  for (Instruction *i : AccessWorkList) {
    Inst = i;

    Value *RawPtr = nullptr;
    Builder->SetInsertPoint(Inst);
    if (LoadInst *LI = dyn_cast<LoadInst>(Inst)) {
      MadeChange |= instrument(LI->getPointerOperand(), LI, DL, RawPtr);
      LI->setOperand(LI->getPointerOperandIndex(), RawPtr);
    } else if (StoreInst *SI = dyn_cast<StoreInst>(Inst)) {
      MadeChange |= instrument(SI->getPointerOperand(), SI->getValueOperand(),
                               DL, RawPtr);
      SI->setOperand(SI->getPointerOperandIndex(), RawPtr);
    } else if (AtomicCmpXchgInst *AI = dyn_cast<AtomicCmpXchgInst>(Inst)) {
      MadeChange |= instrument(AI->getPointerOperand(), AI->getCompareOperand(),
                               DL, RawPtr);
      AI->setOperand(AI->getPointerOperandIndex(), RawPtr);
    } else if (AtomicRMWInst *AI = dyn_cast<AtomicRMWInst>(Inst)) {
      MadeChange |=
          instrument(AI->getPointerOperand(), AI->getValOperand(), DL, RawPtr);
      AI->setOperand(AI->getPointerOperandIndex(), RawPtr);
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

using namespace seahorn;
using namespace llvm;
INITIALIZE_PASS(FatBufferBoundsCheck, "fat-buffer-bounds-instrument",
                "Bounds checking based on extended pointer", false, false)
