/**  The transformation we do here looks roughly like this:
        memcpy(Dst, Source, sizeof(BufferTy))
          goes to
      for each field_id in fields(BufferTy):
        *GEP(Dst, field_id) = *GEP(Src, field_id)
*/
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BuildLibCalls.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/SimplifyLibCalls.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#define PMCPY_LOG(...) LOG("promote-memcpy", __VA_ARGS__)
#define PMCPY_DBG_LOG(...) LOG("promote-memcpy.dbg", __VA_ARGS__)

using namespace llvm;

// -- Gate for the PromoteMemcpy transformation. Off by default; verify-c-common
// -- turns it on via sea.yaml. When on, only the sound (direct GEP) struct-type
// -- recovery is used.
static llvm::cl::opt<bool> PromoteMemcpyEnabled(
    "horn-promote-memcpy",
    llvm::cl::desc("Lower constant-length whole-struct memcpy into field-wise "
                   "loads/stores (struct type recovered only from a GEP on the "
                   "same pointer; sound)"),
    llvm::cl::init(false));

namespace {
class PromoteMemcpy : public FunctionPass {
public:
  static char ID;

  PromoteMemcpy() : FunctionPass(ID) {}

  bool runOnFunction(Function &F) override;
  bool runImpl(Function &F, DominatorTree &DT, AssumptionCache &AC);

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesCFG();
    AU.addRequired<llvm::DominatorTreeWrapperPass>();
    AU.addRequired<AssumptionCacheTracker>();
  }

  StringRef getPassName() const override { return "PromoteMemcpy"; }

private:
  Module *m_M = nullptr;
  LLVMContext *m_Ctx = nullptr;
  const DataLayout *m_DL = nullptr;
  DominatorTree *m_DT = nullptr;
  AssumptionCache *m_AC = nullptr;

  bool simplifyMemCpy(MemCpyInst *MCpy);
  // -- Recover the aggregate (struct) type copied by a memcpy of `Size` bytes.
  // -- Under LLVM opaque pointers the pointee type is no longer available from
  // -- the pointer type, so it is recovered from GEPs in the same function.
  StructType *recoverStructType(Value *SrcPtr, Value *DstPtr, uint64_t Size,
                                Function &F);
  // -- Emit a field-wise copy of aggregate type `Ty` from `Src` to `Dst`.
  void emitFieldwiseCopy(IRBuilder<> &Builder, Type *Ty, Value *Src, Value *Dst,
                         const Twine &SrcName);
};

char PromoteMemcpy::ID = 0;

StructType *PromoteMemcpy::recoverStructType(Value *SrcPtr, Value *DstPtr,
                                             uint64_t Size, Function &F) {
  // -- Legacy typed pointers: the pointee type is available directly.
  for (Value *P : {SrcPtr, DstPtr}) {
    auto *PtrTy = cast<PointerType>(P->getType());
    if (!PtrTy->isOpaque()) {
      if (auto *ST =
              dyn_cast<StructType>(PtrTy->getNonOpaquePointerElementType()))
        if (m_DL->getTypeStoreSize(ST) == Size)
          return ST;
    }
  }

  // -- Opaque pointers: the pointee type is gone. Recover it ONLY from a GEP
  // -- that indexes the very pointer copied by the memcpy, with a struct whose
  // -- store size matches the length. This is sound: the IR itself uses that
  // -- pointer as this struct type. Matching merely by size (a different struct
  // -- of equal width, or one reached through a shared stack slot) would be
  // -- unsound and is intentionally not attempted -- if no such GEP exists we
  // -- bail and let the operational semantics handle the raw memcpy.
  for (auto &I : llvm::instructions(F)) {
    auto *GEP = dyn_cast<GetElementPtrInst>(&I);
    if (!GEP)
      continue;
    auto *ST = dyn_cast<StructType>(GEP->getSourceElementType());
    if (!ST || m_DL->getTypeStoreSize(ST) != Size)
      continue;
    Value *Base = GEP->getPointerOperand();
    if (Base == SrcPtr || Base == DstPtr)
      return ST;
  }
  return nullptr;
}

void PromoteMemcpy::emitFieldwiseCopy(IRBuilder<> &Builder, Type *Ty,
                                      Value *Src, Value *Dst,
                                      const Twine &SrcName) {
  auto *ST = dyn_cast<StructType>(Ty);
  if (!ST) {
    auto *NewLoad = Builder.CreateLoad(Ty, Src, SrcName + ".pmcpy");
    auto *NewStore = Builder.CreateStore(NewLoad, Dst);
    PMCPY_DBG_LOG(errs() << "New load-store:\n\t"; NewLoad->print(errs());
                  errs() << "\n\t"; NewStore->print(errs()); errs() << "\n");
    return;
  }

  auto *I32Ty = IntegerType::getInt32Ty(*m_Ctx);
  auto *Zero = ConstantInt::get(I32Ty, 0);
  for (unsigned i = 0, e = ST->getNumElements(); i != e; ++i) {
    auto *Idx = ConstantInt::get(I32Ty, i);
    auto *SrcGEP =
        Builder.CreateInBoundsGEP(ST, Src, {Zero, Idx}, "src.gep.pmcpy");
    auto *DstGEP =
        Builder.CreateInBoundsGEP(ST, Dst, {Zero, Idx}, "buffer.gep.pmcpy");
    emitFieldwiseCopy(Builder, ST->getElementType(i), SrcGEP, DstGEP, SrcName);
  }
}

bool PromoteMemcpy::simplifyMemCpy(MemCpyInst *MI) {
  assert(MI);

  // skip non-constant length memcpy()
  ConstantInt *MemOpLength = dyn_cast<ConstantInt>(MI->getLength());
  if (!MemOpLength)
    return false;

  uint64_t Size = MemOpLength->getLimitedValue();
  if (Size == 0) {
    PMCPY_LOG(WARN << "unexpected 0 length memcpy: " << *MI;);
    return false;
  }

  auto *SrcPtr = MI->getSource();
  auto *DstPtr = MI->getDest();

  unsigned SrcAddrSp = cast<PointerType>(SrcPtr->getType())->getAddressSpace();
  unsigned DstAddrSp = cast<PointerType>(DstPtr->getType())->getAddressSpace();
  if (SrcAddrSp != DstAddrSp) {
    PMCPY_LOG(WARN << "memcpy across address spaces: " << *MI;);
    return false;
  }

  // -- Determine the aggregate type being copied. Under opaque pointers this is
  // -- recovered from surrounding GEPs rather than the pointer type.
  StructType *BufferTy =
      recoverStructType(SrcPtr, DstPtr, Size, *MI->getFunction());
  if (!BufferTy) {
    PMCPY_LOG(WARN << "could not recover struct type for memcpy: " << *MI;);
    return false;
  }
  // require constant length argument equal to struct size
  if (m_DL->getTypeStoreSize(BufferTy) != Size) {
    PMCPY_LOG(WARN << "memcpy length not equal to struct size: " << *MI;);
    return false;
  }

  PMCPY_DBG_LOG(errs() << "\nLowering memcpy of "; BufferTy->print(errs());
                errs() << "\n\tSrc:\t"; SrcPtr->print(errs());
                errs() << "\n\tDst:\t"; DstPtr->print(errs()); errs() << "\n";
                errs().flush());

  // Perform field-wise copy, recursing into nested structs:
  //   memcpy(Dst, Src, sizeof(BufferTy))
  //    ||
  //    V
  // for each field_id in fields(BufferTy):
  //   *GEP(Dst, field_id) = *GEP(Src, field_id)
  IRBuilder<> Builder(MI);
  emitFieldwiseCopy(Builder, BufferTy, SrcPtr, DstPtr, SrcPtr->getName());
  return true;
}

bool PromoteMemcpy::runOnFunction(Function &F) {
  if (!PromoteMemcpyEnabled)
    return false;
  if (F.empty())
    return false;
  return runImpl(F, getAnalysis<DominatorTreeWrapperPass>().getDomTree(),
                 getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F));
}

bool PromoteMemcpy::runImpl(Function &F, DominatorTree &DT,
                            AssumptionCache &AC) {
  m_DT = &DT;
  m_M = F.getParent();
  m_Ctx = &m_M->getContext();
  m_DL = &m_M->getDataLayout();
  m_AC = &AC;

  bool Changed = false;
  SmallVector<MemCpyInst *, 8> ToDeleteQueue;
  PMCPY_DBG_LOG(
      errs() << "\n############## Start Promote Memcpy ###################\n");

  for (auto &BB : F)
    for (auto &I : BB)
      if (auto *MCpy = dyn_cast<MemCpyInst>(&I)) {
        PMCPY_DBG_LOG(MCpy->print(errs() << "Visiting: \n"); errs() << "\n");

        if (!simplifyMemCpy(MCpy))
          continue;

        ToDeleteQueue.push_back(MCpy);
        Changed = true;
      }

  PMCPY_DBG_LOG(errs() << "Removing dead memcpys in " << F.getName() << ":");
  for (auto *MCpy : ToDeleteQueue) {
    PMCPY_DBG_LOG(MCpy->print(errs() << "\n\t"));

    // Using getArgOperand API to avoid looking through casts.
    auto *SrcPtr = dyn_cast<BitCastInst>(MCpy->getArgOperand(1));
    auto *DstPtr = dyn_cast<BitCastInst>(MCpy->getArgOperand(0));

    MCpy->eraseFromParent();
    if (SrcPtr && SrcPtr->hasNUses(0)) {
      PMCPY_DBG_LOG(SrcPtr->print(errs() << "\n\t\tdeleting:\t"));
      SrcPtr->eraseFromParent();
    }
    if (DstPtr && DstPtr->hasNUses(0)) {
      PMCPY_DBG_LOG(DstPtr->print(errs() << "\n\t\tdeleting:\t"));
      DstPtr->eraseFromParent();
    }
  }

  PMCPY_DBG_LOG(
      errs() << "\n############## End Promote Memcpy ###################\n";
      errs().flush());
  return Changed;
}

} // namespace

namespace seahorn {
llvm::FunctionPass *createPromoteMemcpyPass() { return new PromoteMemcpy(); }
} // namespace seahorn

static llvm::RegisterPass<PromoteMemcpy>
    X("promote-memcpy", "Promote memcpy to field-wise stores");

// --- new pass manager wrapper ---
#include "seahorn/SeaNewPmPasses.hh"
llvm::PreservedAnalyses
seahorn::PromoteMemcpyPass::run(llvm::Function &F,
                                llvm::FunctionAnalysisManager &FAM) {
  bool changed =
      PromoteMemcpy().runImpl(F, FAM.getResult<llvm::DominatorTreeAnalysis>(F),
                              FAM.getResult<llvm::AssumptionAnalysis>(F));
  return changed ? llvm::PreservedAnalyses::none()
                 : llvm::PreservedAnalyses::all();
}
