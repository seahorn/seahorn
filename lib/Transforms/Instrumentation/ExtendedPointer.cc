//===- ExtendedPointer.cpp - Instrumentation for run-time bounds checking --===//
//
//                     The LLVM Compiler Infrastructure
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
//
// This file implements a pass that instruments the code to perform run-time
// bounds checking on loads, stores, and other memory intrinsics.
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

#include "seahorn/Support/SeaLog.hh"

#include "seahorn/config.h"
using namespace llvm;

#define DEBUG_TYPE "sea-bounds-checking"
#define SEA_SET_FAT_SLOT0 "__sea_set_extptr_slot0"
#define SEA_GET_FAT_SLOT0 "__sea_get_extptr_slot0"
#define SEA_SET_FAT_SLOT1 "__sea_set_extptr_slot1"
#define SEA_GET_FAT_SLOT1 "__sea_get_extptr_slot1"
#define SEA_COPY_FAT_SLOTS "__sea_copy_extptr_slots"


//static cl::opt<bool> SingleErrorBB("bounds-checking-single-trap",
//                                  cl::desc("Use one trap block per function"));

STATISTIC(ChecksAdded, "Bounds checks added");
STATISTIC(ChecksSkipped, "Bounds checks skipped");
STATISTIC(ChecksUnable, "Bounds checks unable to add");

typedef IRBuilder<TargetFolder> BuilderTy;

namespace {
struct ExtendedPointer : public FunctionPass {
  static char ID;
  ExtendedPointer() : FunctionPass(ID){}

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
  Function* m_setFatSlot0; // set ptr base
  Function* m_setFatSlot1; // set ptr size
  Function* m_getFatSlot0; // get ptr base
  Function* m_getFatSlot1; // get ptr size
  Function* m_copyFatSlots; // copy ptr info


  BasicBlock *getErrorBB();
  void emitBranchToTrap(Value *Cmp = nullptr);
  bool instrument(Value *Ptr, Value *Val, const DataLayout &DL);
  bool instrumentAddress(Value *Ptr, const DataLayout &DL, Value *BasePtr = nullptr);
  Value* memToShadow(Value *mem, BuilderTy *builder);
};
}

char ExtendedPointer::ID = 0;

/// getErrorBB - create a basic block that traps. All overflowing conditions
/// branch to this block. There's only one trap block per function.
BasicBlock *ExtendedPointer::getErrorBB() {
  if (ErrorBB)
    return ErrorBB;

  Function *Fn = Inst->getParent()->getParent();
  Module *Md = Fn->getParent();
  LLVMContext &ctx = Md->getContext();
  IRBuilder<>::InsertPointGuard Guard(*Builder);
  ErrorBB = BasicBlock::Create(Fn->getContext(), "bound_overflow", Fn);
  Builder->SetInsertPoint(ErrorBB);

//  llvm::Value *F = Intrinsic::getDeclaration(Fn->getParent(), Intrinsic::trap);
  AttrBuilder AB;
  AB.addAttribute(Attribute::NoReturn);
  AttributeList as = AttributeList::get(ctx, AttributeList::FunctionIndex, AB);
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
void ExtendedPointer::emitBranchToTrap(Value *Cmp) {
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
bool ExtendedPointer::instrument(Value *Ptr, Value *InstVal,
                                const DataLayout &DL) {
  uint64_t NeededSize = DL.getTypeStoreSize(InstVal->getType());
  Type *IntTy = DL.getIntPtrType(Ptr->getType());
  Value *NeededSizeVal = ConstantInt::get(IntTy, NeededSize);
  DEBUG(dbgs() << "Instrument " << *Ptr << " for " << Twine(NeededSize)
               << " bytes\n");

  SizeOffsetEvalType SizeOffset = ObjSizeEval->compute(Ptr);
  Value *Or;
  if (!ObjSizeEval->bothKnown(SizeOffset)) {
    WARN << "fatptr instrument " << *Ptr << " for " << Twine(NeededSize) << " bytes\n";
    // get start and end by calling internalized functions
    Value *Start = Builder->CreateCall(m_getFatSlot0, Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
    Value *Size = Builder->CreateCall(m_getFatSlot1, Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()));
    Value *PtrInt = Builder->CreatePtrToInt(Ptr, IntTy);
    // Ptr >= Start
    Value *CmpUnderFlow = Builder->CreateICmpULT(PtrInt, Builder->CreateIntCast(Start, IntTy, true));
    // Start + Size >= Ptr + NeededSize
    Value *accessEnd = Builder->CreateAdd(PtrInt, NeededSizeVal);
    Value *ptrEnd = Builder->CreateAdd(Start, Size);
    Value *CmpOverFlow = Builder->CreateICmpULT(Builder->CreateIntCast(ptrEnd, IntTy, true), accessEnd);
    Or = Builder->CreateOr(CmpUnderFlow, CmpOverFlow);
  } else {
    // size and offest statically computed
    WARN << "statically instrument " << *Ptr << " for " << Twine(NeededSize) << " bytes\n";
    Value *Size   = SizeOffset.first;
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
      Value *Cmp1 = Builder->CreateICmpSLT(Offset, ConstantInt::get(IntTy, 0));
      Or = Builder->CreateOr(Cmp1, Or);
    }
  }
  emitBranchToTrap(Or);

  return true;
}

/* Record information of address Ptr, store/update the base address and size */
bool ExtendedPointer::instrumentAddress(Value *Ptr, const DataLayout &DL,
                                        Value *BasePtr) {
  if (!BasePtr) {
    Type *IntTy = DL.getIntPtrType(Ptr->getType());
    // set_fat_slot0(Ptr, Base)
    Builder->CreateCall(
      m_setFatSlot0,
      {
        Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()),
        Builder->CreatePtrToInt(Ptr, Builder->getInt32Ty())
      }
    );
    Value *sizeVal;
    // alloca
    if (auto *ALI = dyn_cast<AllocaInst>(Ptr)) {
      uint64_t size = DL.getTypeStoreSize(ALI->getAllocatedType());
      sizeVal = ConstantInt::get(Type::getInt32Ty(*Ctx), size);
    } else {
      llvm_unreachable("unexpected lack of base address");
    }
    // set_fat_slot1(Ptr, Size)
    Builder->CreateCall(
      m_setFatSlot1,
      {
        Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()),
        sizeVal
      }
    );
  } else {
    // copy_fat_slots(Ptr, BasePtr)
    Builder->CreateCall(
      m_copyFatSlots,
      {
        Builder->CreateBitCast(Ptr, Builder->getInt8PtrTy()),
        Builder->CreateBitCast(BasePtr, Builder->getInt8PtrTy()),
      }
    );
  }

  return true;
}

bool ExtendedPointer::runOnFunction(Function &F) {
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
    SEA_GET_FAT_SLOT0, Type::getInt32Ty(*Ctx), Type::getInt8PtrTy(*Ctx, 0)));
  m_getFatSlot1 = cast<Function>(Mod->getOrInsertFunction(
    SEA_GET_FAT_SLOT1, Type::getInt32Ty(*Ctx), Type::getInt8PtrTy(*Ctx, 0)));

  m_setFatSlot0 = cast<Function>(Mod->getOrInsertFunction(
    SEA_SET_FAT_SLOT0,
    Type::getVoidTy(*Ctx),
    Type::getInt8PtrTy(*Ctx, 0),
    Type::getInt32Ty(*Ctx)
  ));
  m_setFatSlot1 = cast<Function>(Mod->getOrInsertFunction(
    SEA_SET_FAT_SLOT1,
    Type::getVoidTy(*Ctx),
    Type::getInt8PtrTy(*Ctx, 0),
    Type::getInt32Ty(*Ctx)
  ));

  m_copyFatSlots = cast<Function>(Mod->getOrInsertFunction(
    SEA_COPY_FAT_SLOTS,
    Type::getVoidTy(*Ctx),
    Type::getInt8PtrTy(*Ctx, 0),
    Type::getInt8PtrTy(*Ctx, 0)
  ));

  // check HANDLE_MEMORY_INST in include/llvm/Instruction.def for memory
  // touching instructions
  std::vector<Instruction*> AccessWorkList;
  std::vector<Instruction*> AddrWorkList; // new register is created for addr
  for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
    Instruction *I = &*i;
    if (isa<LoadInst>(I) || isa<StoreInst>(I) || isa<AtomicCmpXchgInst>(I) ||
        isa<AtomicRMWInst>(I)) {
      AccessWorkList.push_back(I);
      continue;
    }
    if (isa<AllocaInst>(I) || isa<GetElementPtrInst>(I)) {
      AddrWorkList.push_back(I);
    }

  }

  bool MadeChange = false;
  for (Instruction *i : AddrWorkList) {
    Inst = i;
    Builder->SetInsertPoint(Inst->getNextNode()); // insert after
    if (AllocaInst *ALI = dyn_cast<AllocaInst>(Inst)) {
      Type* allocTy = ALI->getAllocatedType();
      if (allocTy->isArrayTy() || allocTy->isPointerTy() || allocTy->isStructTy()) {
        MadeChange |= instrumentAddress(ALI, DL);
      }
    } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(Inst)){
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
    } else if (StoreInst *SI = dyn_cast<StoreInst>(Inst)) {
      MadeChange |=
          instrument(SI->getPointerOperand(), SI->getValueOperand(), DL);
    } else if (AtomicCmpXchgInst *AI = dyn_cast<AtomicCmpXchgInst>(Inst)) {
      MadeChange |=
          instrument(AI->getPointerOperand(), AI->getCompareOperand(), DL);
    } else if (AtomicRMWInst *AI = dyn_cast<AtomicRMWInst>(Inst)) {
      MadeChange |=
          instrument(AI->getPointerOperand(), AI->getValOperand(), DL);
    } else {
      llvm_unreachable("unknown Instruction type");
    }
  }
  return MadeChange;
}
namespace seahorn {
FunctionPass *createSeaExtendedPointerPass() { return new ExtendedPointer(); }
}

static RegisterPass<ExtendedPointer>
    X("extended-pointer-pass", "Bounds checking based on extended pointer");

