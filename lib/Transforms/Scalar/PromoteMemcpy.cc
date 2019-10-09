/**  The transformation we do here looks roughly like this:
        memcpy(Dst, Source, sizeof(BufferTy))
          goes to
      for each field_id in fields(BufferTy):
        *GEP(Dst, field_id) = *GEP(Src, field_id)
*/
#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/IRBuilder.h"
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

namespace {
class PromoteMemcpy : public FunctionPass {
public:
  static char ID;

  PromoteMemcpy() : FunctionPass(ID) {}

  bool runOnFunction(Function &F);

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
};

char PromoteMemcpy::ID = 0;

bool PromoteMemcpy::simplifyMemCpy(MemCpyInst *MI) {
  assert(MI);

  unsigned DstAlign = getKnownAlignment(MI->getDest(), *m_DL, MI, m_AC, m_DT);
  unsigned SrcAlign = getKnownAlignment(MI->getSource(), *m_DL, MI, m_AC, m_DT);
  unsigned MinAlign = std::min(DstAlign, SrcAlign);
  unsigned CopyAlign = MI->getAlignment();

  if (CopyAlign < MinAlign) {
    PMCPY_LOG(WARN << "unhandled alignment. Skipping memcpy: " << *MI;);
    return false;
  }

  // skip non-constant length memcpy()
  ConstantInt *MemOpLength = dyn_cast<ConstantInt>(MI->getLength());
  if (!MemOpLength) {
    return false;
  }

  // Source and destination pointer types are always "i8*" for intrinsic.  See
  // if the size is something we can handle with a single primitive load/store.
  // A single load+store correctly handles overlapping memory in the memmove
  // case.
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
    llvm_unreachable("unexpected");
    return false;
  }

  auto *SrcPtrTy = cast<PointerType>(SrcPtr->getType());
  auto *DstPtrTy = cast<PointerType>(DstPtr->getType());

  if (SrcPtrTy != DstPtrTy) {
    PMCPY_LOG(WARN << "memcpy between different types: " << *MI;);
    return false;
  }

  if (!SrcPtrTy->getPointerElementType()->isFirstClassType()) {
    PMCPY_LOG(WARN << "Not a first class type! " << *MI;);
    return false;
  }

  PMCPY_DBG_LOG(errs() << "\nSrc:\t"; SrcPtr->print(errs());
                SrcPtrTy->print(errs() << "\t"); errs() << "\nDst:\t";
                DstPtr->print(errs()); DstPtrTy->print(errs() << "\t");
                errs() << "\n"; errs().flush());

  auto *BufferTy = dyn_cast<StructType>(SrcPtrTy->getPointerElementType());
  // require src to be a struct
  if (!BufferTy)
    return false;

  IRBuilder<> Builder(MI);
  auto *I64Ty = IntegerType::getInt64Ty(*m_Ctx);
  auto *NullInt = Constant::getNullValue(I64Ty);
  auto *I32Ty = IntegerType::getInt32Ty(*m_Ctx);

  // Perform field-wise copy. Note that this doesn't recurse and only explores
  // the immediately visible fields.
  //
  // The transformation we do here looks roughly like this:
  //   memcpy(Dst, Source, sizeof(BufferTy))
  //    ||
  //    V
  // for each field_id in fields(BufferTy):
  //   *GEP(Dst, field_id) = *GEP(Src, field_id)
  //

  using Transfer = std::pair<Value *, Value *>;
  SmallVector<Transfer, 4> ToLower = {std::make_pair(SrcPtr, DstPtr)};
  while (!ToLower.empty()) {
    Value *TrSrc, *TrDst;
    std::tie(TrSrc, TrDst) = ToLower.pop_back_val();
    auto *Ty = TrSrc->getType();
    assert(Ty == TrDst->getType());

    if (!Ty->isStructTy()) {
      auto *NewLoad = Builder.CreateLoad(TrSrc, SrcPtr->getName() + ".pmcpy");
      auto *NewStore = Builder.CreateStore(NewLoad, TrDst);

      PMCPY_DBG_LOG(errs() << "New load-store:\n\t"; NewLoad->print(errs());
                    errs() << "\n\t"; NewStore->print(errs()); errs() << "\n");
      continue;
    }

    SmallVector<Transfer, 8> TmpBuff;
    for (unsigned i = 0, e = Ty->getStructNumElements(); i != e; ++i) {
      auto *Idx = Constant::getIntegerValue(I32Ty, APInt(32, i));
      auto *SrcGEP = Builder.CreateInBoundsGEP(nullptr, SrcPtr, {NullInt, Idx},
                                               "src.gep.pmcpy");
      auto *DstGEP = Builder.CreateInBoundsGEP(nullptr, DstPtr, {NullInt, Idx},
                                               "buffer.gep.pmcpy");
      TmpBuff.push_back({SrcGEP, DstGEP});
    }

    for (auto &P : llvm::reverse(TmpBuff))
      ToLower.push_back(P);

    PMCPY_DBG_LOG(errs() << "\tSecond level\n");
  }
  return true;
}

bool PromoteMemcpy::runOnFunction(Function &F) {
  if (F.empty())
    return false;

  m_DT = &getAnalysis<DominatorTreeWrapperPass>().getDomTree();
  m_M = F.getParent();
  m_Ctx = &m_M->getContext();
  m_DL = &m_M->getDataLayout();
  m_AC = &getAnalysis<AssumptionCacheTracker>().getAssumptionCache(F);

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
