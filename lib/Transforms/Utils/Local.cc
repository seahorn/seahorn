#include "seahorn/Transforms/Utils/Local.hh"

#include "seahorn/Analysis/SeaBuiltinsInfo.hh"

#include "llvm/IR/CFG.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Transforms/Utils/Local.h"

using namespace llvm;

namespace seahorn {
/// Returns all basic blocks that are ancestors of the blocks in roots
void markAncestorBlocks(ArrayRef<const BasicBlock *> roots,
                        DenseSet<const BasicBlock *> &visited) {
  SmallVector<const BasicBlock *, 128> W(std::begin(roots), std::end(roots));

  while (!W.empty()) {
    const BasicBlock *bb = W.back();
    W.pop_back();
    if (visited.count(bb) > 0)
      continue;
    visited.insert(bb);
    std::copy(pred_begin(bb), pred_end(bb), std::back_inserter(W));
  }
}

/// Reduce the given function to the basic blocks in a given region
void reduceToRegion(Function &F, DenseSet<const BasicBlock *> &region,
                    SeaBuiltinsInfo &SBI) {
  std::vector<BasicBlock *> dead;
  dead.reserve(F.size());

  IRBuilder<> Builder(F.getContext());
  Module *M = F.getParent();
  assert(M);
  auto *assumeFn = SBI.mkSeaBuiltinFn(SeaBuiltinsOp::ASSUME, *M);
  auto *assumeNotFn = SBI.mkSeaBuiltinFn(SeaBuiltinsOp::ASSUME_NOT, *M);

  for (BasicBlock &BB : F) {

    if (region.count(&BB) <= 0) {
      dead.push_back(&BB);
      auto *BBTerm = BB.getTerminator();
      for (unsigned i = 0, e = BBTerm->getNumSuccessors(); i != e; ++i)
        BBTerm->getSuccessor(i)->removePredecessor(&BB);
      continue;
    }

    if (BranchInst *br = dyn_cast<BranchInst>(BB.getTerminator())) {
      if (br->isUnconditional())
        continue;
      BasicBlock *s0 = br->getSuccessor(0);
      BasicBlock *s1 = br->getSuccessor(1);

      BasicBlock *kill = NULL;

      if (region.count(s0) <= 0)
        kill = s0;
      else if (region.count(s1) <= 0)
        kill = s1;
      else
        continue;

      Builder.SetInsertPoint(&BB, br->getIterator());
      CallInst *ci = Builder.CreateCall(kill == s1 ? assumeFn : assumeNotFn,
                                        br->getCondition());
      ci->setDebugLoc(br->getDebugLoc());
      kill->removePredecessor(&BB);
      br->eraseFromParent();
      Builder.SetInsertPoint(&BB);
      Builder.CreateBr(kill == s1 ? s0 : s1);
    }
  }

  for (auto BB : dead) {
    BB->dropAllReferences();
  }

  for (auto *bb : dead) {
    if (bb->hasNUses(0))
      bb->eraseFromParent();
    else {
      errs()
          << "WARNING: attempt to delete a basic block that is still in use.\n"
          << "Perhaps the user is an invoke instructions with an out-of-region"
          << " landing block. Consider lowering invoke instructions.\n";

      errs() << "bb: " << bb->getName() << "\n";
      errs() << "Users:\n";
      auto UI = bb->user_begin();
      auto E = bb->user_end();
      for (; UI != E; ++UI)
        errs() << *(*UI) << "\n";
    }
  }

  // -- no metatdata for declarations && empty functions are declarations
  if (F.empty() && F.hasMetadata())
    F.clearMetadata();
}

/// Reduce the function to only the BasicBlocks that are ancestors of exits
void reduceToAncestors(Function &F, ArrayRef<const BasicBlock *> exits,
                       SeaBuiltinsInfo &SBI) {
  removeUnreachableBlocks(F);
  DenseSet<const BasicBlock *> region;
  markAncestorBlocks(exits, region);
  reduceToRegion(F, region, SBI);
}

void reduceToReturnPaths(Function &F, SeaBuiltinsInfo &SBI) {
  if (F.isDeclaration())
    return;

  SmallVector<const BasicBlock *, 16> exits;

  for (auto &BB : F)
    if (isa<ReturnInst>(BB.getTerminator()))
      exits.push_back(&BB);
  reduceToAncestors(F, exits, SBI);
}

/// work around bug in llvm::RecursivelyDeleteTriviallyDeadInstructions
bool RecursivelyDeleteTriviallyDeadInstructions(Value *V,
                                                const TargetLibraryInfo *TLI) {
  Instruction *I = dyn_cast<Instruction>(V);

  return false;
  if (!I->getParent())
    return false;
  return llvm::RecursivelyDeleteTriviallyDeadInstructions(V, TLI);
}

bool HasReturn(BasicBlock &bb, ReturnInst *&retInst) {
  if (auto *ret = dyn_cast<ReturnInst>(bb.getTerminator())) {
    retInst = ret;
    return true;
  }
  return false;
}

bool HasReturn(Function &F, ReturnInst *&retInst) {
  for (auto &bb : F) {
    if (HasReturn(bb, retInst))
      return true;
  }
  return false;
}

bool HasUniqueReturn(Function &F, ReturnInst *&retInst) {
  bool found = false;

  for (auto &bb : F) {
    if (HasReturn(bb, retInst)) {
      // -- already found another one, so not unique
      if (found)
        return false;
      found = true;
    }
  }
  return found;
}
} // namespace seahorn
