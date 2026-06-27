/// New pass-manager reimplementation of LLVM's legacy-only StripDeadDebugInfo
/// pass. LLVM 16 ships StripDeadDebugInfo as a legacy ModulePass with no new-PM
/// equivalent, so SeaHorn provides its own so seapp's pipeline stays entirely on
/// the new pass manager.
///
/// The transform prunes, from every DICompileUnit, the global-variable debug
/// entries that are no longer attached to any live GlobalVariable -- mirroring
/// the behaviour of llvm::createStripDeadDebugInfoPass().
#include "seahorn/SeaNewPmPasses.hh"

#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugInfoMetadata.h"
#include "llvm/IR/GlobalVariable.h"
#include "llvm/IR/Module.h"

#include <set>

using namespace llvm;

namespace {
bool stripDeadDebugInfoImpl(Module &M) {
  bool Changed = false;
  LLVMContext &C = M.getContext();

  // -- Collect the global-variable debug expressions that are still attached to
  // -- a live GlobalVariable.
  std::set<DIGlobalVariableExpression *> LiveGVs;
  for (GlobalVariable &GV : M.globals()) {
    SmallVector<DIGlobalVariableExpression *, 1> GVEs;
    GV.getDebugInfo(GVEs);
    for (auto *GVE : GVEs)
      LiveGVs.insert(GVE);
  }

  NamedMDNode *NMD = M.getNamedMetadata("llvm.dbg.cu");
  if (!NMD)
    return false;

  SmallVector<Metadata *, 64> LiveGlobalVariables;
  DenseSet<DIGlobalVariableExpression *> VisitedSet;

  for (MDNode *N : NMD->operands()) {
    auto *DIC = cast<DICompileUnit>(N);

    bool GlobalVariableChange = false;
    for (auto *DIG : DIC->getGlobalVariables()) {
      // -- Visit each global-variable entry only once.
      if (!VisitedSet.insert(DIG).second)
        continue;

      // -- Keep entries still referenced by a live GlobalVariable (or that are
      // -- constant expressions, which carry their own value).
      if (LiveGVs.count(DIG) ||
          (DIG->getExpression() && DIG->getExpression()->isConstant()))
        LiveGlobalVariables.push_back(DIG);
      else
        GlobalVariableChange = true;
    }

    if (GlobalVariableChange) {
      DIC->replaceGlobalVariables(MDTuple::get(C, LiveGlobalVariables));
      Changed = true;
    }

    LiveGlobalVariables.clear();
  }

  return Changed;
}
} // namespace

llvm::PreservedAnalyses
seahorn::SeaStripDeadDebugInfoPass::run(llvm::Module &M,
                                        llvm::ModuleAnalysisManager &) {
  return stripDeadDebugInfoImpl(M) ? llvm::PreservedAnalyses::none()
                                   : llvm::PreservedAnalyses::all();
}
