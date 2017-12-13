#include "seahorn/Transforms/Instrumentation/SimpleMemoryCheck.hh"

#include "llvm/ADT/DenseMap.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"

#include "seahorn/config.h"

#include "seahorn/Analysis/CanAccessMemory.hh"
#include "ufo/Passes/NameValues.hpp"

#include "llvm/ADT/SmallSet.h"
#include "llvm/ADT/SmallVector.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "boost/format.hpp"

// Seahorn dsa
#include "sea_dsa/DsaAnalysis.hh"
// Llvm dsa
#include "seahorn/Support/DSAInfo.hh"

using namespace llvm;

namespace seahorn {


struct PtrOrigin {
  llvm::Value *Ptr;
  int64_t Offset;

  void dump() const {
    llvm::dbgs() << '<';
    if (Ptr) Ptr->print(dbgs());
    else dbgs() << "nullptr";
    dbgs() << ", " << Offset << ">\n";
  }
};


class SimpleMemoryCheck : public llvm::ModulePass {
public:
  static char ID;
  SimpleMemoryCheck() : llvm::ModulePass(ID) {}
  virtual bool runOnModule(llvm::Module &M);
  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const;
  virtual const char *getPassName() const { return "SimpleMemoryCheck"; }

private:
  LLVMContext *Ctx;
  const DataLayout *DL;
  const TargetLibraryInfo *TLI;

  bool isKnownAlloc(Value *Ptr);
  llvm::Optional<size_t> getAllocSize(Value *Ptr);
  PtrOrigin trackPtrOrigin(Value *Ptr);
  bool canBeUnsafe(Value *Ptr);
};

llvm::ModulePass *CreateSimpleMemoryCheckPass() {
  return new SimpleMemoryCheck();
}


bool SimpleMemoryCheck::isKnownAlloc(Value *Ptr) {
  if (auto *AI = dyn_cast<AllocaInst>(Ptr)) {
    if (AI->isArrayAllocation())
      return false;

    return true;
  }

  auto *CI = dyn_cast<CallInst>(Ptr);
  if (CI && isAllocationFn(CI, TLI))
    return true;

  return false;
}

llvm::Optional<size_t> SimpleMemoryCheck::getAllocSize(Value *Ptr) {
  assert(Ptr);
  if (!isKnownAlloc(Ptr))
    return None;


  ObjectSizeOffsetEvaluator OSOE(*DL, TLI, *Ctx, true);
  SizeOffsetEvalType OffsetAlign = OSOE.compute(Ptr);
  if (!OSOE.knownSize(OffsetAlign))
    return llvm::None;

  if (auto *Sz = dyn_cast<ConstantInt>(OffsetAlign.first)) {
    const int64_t I = Sz->getSExtValue();
    dbgs() << "\tconstant size: " << I << "\n";

    assert(I >= 0);
    return size_t(I);
  }

  return llvm::None;
}

PtrOrigin SimpleMemoryCheck::trackPtrOrigin(Value *Ptr) {
  assert(Ptr);

  PtrOrigin Res{Ptr, 0};
  unsigned Iter = 0;
  while (true) {
    ++Iter;
    for (unsigned i = 0; i < Iter; ++i) dbgs() << "\t";
    Res.dump();

    if (isKnownAlloc(Res.Ptr))
      return Res;

    if (isa<CallInst>(Res.Ptr)) {
      dbgs() << "Call, giving up :<\n";
      return Res;
    }

    if (auto *LD = dyn_cast<LoadInst>(Res.Ptr)) {
      dbgs() << "Load, giving up :<\n";
      return Res;
    }

    if (isa<PHINode>(Res.Ptr)) {
      dbgs() << "Phi node, giving up :<\n";
      return Res;
    }

    if (auto *BC = dyn_cast<BitCastInst>(Res.Ptr)) {
      auto *Arg = BC->getOperand(0);
      Res.Ptr = Arg;
      continue;
    }

    if (auto *GEP = dyn_cast<GetElementPtrInst>(Res.Ptr)) {
      auto *Arg = GEP->getOperand(0);

      APInt GEPOffset(DL->getPointerTypeSizeInBits(GEP->getType()), 0);
      if (!GEP->accumulateConstantOffset(*DL, GEPOffset)) {
        dbgs() << "Non-constant GEP, giving up\n";
        return Res;
      }

      Res.Ptr = Arg;
      Res.Offset += GEPOffset.getSExtValue();
      continue;
    }

    Res.Ptr->dump();
    dbgs() << "Unhandled instruction type!\n";
    return Res;
  }
}

bool SimpleMemoryCheck::canBeUnsafe(Value *Ptr) {
  assert(isa<LoadInst>(Ptr) || isa<StoreInst>(Ptr) && "Wrong instruction type");

  auto *Inst = dyn_cast<Instruction>(Ptr);
  assert(Inst);
  Value *Arg = Inst->getOperand(0);
  assert(Arg);

  PtrOrigin Origin = trackPtrOrigin(Arg);
  Optional<size_t> AllocSize = getAllocSize(Origin.Ptr);
  if (!AllocSize)
    return false;

  auto *L = dyn_cast<LoadInst>(Inst);
  assert(L && "Only loads for now");

  auto *Ty = L->getType();
  assert(Ty);

  const uint32_t Sz = DL->getTypeSizeInBits(Ty) / 8;
  if (int64_t(Origin.Offset) + Sz > int64_t(*AllocSize)) {
    dbgs() << "Allocated: " << (*AllocSize) << ", load size " << Sz
           << " at offset " << Origin.Offset << "\n";
    return true;
  }

  return false;
}

bool SimpleMemoryCheck::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  Function *main = M.getFunction("main");
  if (!main) {
    errs() << "Main not found: no buffer overflow checks added\n";
    return false;
  }

  Ctx = &M.getContext();
  TLI = &getAnalysis<TargetLibraryInfoWrapperPass>().getTLI();
  DL = &M.getDataLayout();

  M.dump();
  llvm::outs() << "\n\n ========== SMC  ==========\n";

  for (auto &F : M) {
    // if (F.getName() != "main") continue;
    // dbgs() << "Found main\n";
    if (F.isDeclaration()) continue;

    //F.viewCFG();

    for (auto &BB : F) {
      for (auto &I : BB) {
        if (auto *L = dyn_cast<LoadInst>(&I)) {
          dbgs() << "\n\nFound a load in " << BB.getName() << ":\t";
          L->dump();

          if (canBeUnsafe(L)) {
            dbgs() << "Can be unsafe: ";
            L->dump();
            dbgs() << "\n";
          }
        }
      }
    }
  }

  errs() << " ========== SMC  ==========\n";
  // errs () << M << "\n";
  return true;
}

void SimpleMemoryCheck::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
  AU.addRequired<seahorn::DSAInfo>();     // run llvm dsa
  AU.addRequired<sea_dsa::DsaInfoPass>(); // run seahorn dsa
  AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
  AU.addRequired<llvm::UnifyFunctionExitNodes>();
  AU.addRequired<llvm::CallGraphWrapperPass>();
  // for debugging
  // AU.addRequired<ufo::NameValues> ();
}

char SimpleMemoryCheck::ID = 0;

static llvm::RegisterPass<SimpleMemoryCheck>
    Y("abc-simple", "Insert array buffer checks using simple encoding");

} // end namespace seahorn
