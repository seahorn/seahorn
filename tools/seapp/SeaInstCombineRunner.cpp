// Isolated translation unit that runs SeaHorn's new-PM SeaInstCombine pass.
//
// This is kept out of seapp.cc on purpose: llvm-seahorn's SeaInstCombine.h
// reuses LLVM's `llvm/Transforms/InstCombine/InstCombine.h` include guard
// (LLVM_TRANSFORMS_INSTCOMBINE_INSTCOMBINE_H). seapp.cc pulls llvm's header via
// LinkAllPasses.h, which would shadow SeaInstCombine.h. This TU never includes
// llvm's InstCombine.h, so SeaInstCombinePass is visible here.

#include "llvm_seahorn/Transforms/InstCombine/SeaInstCombine.h"
// SeaInstCombine.h sets DEBUG_TYPE at file scope; don't leak it into the
// LLVM headers below.
#ifdef DEBUG_TYPE
#undef DEBUG_TYPE
#endif

#include "llvm/IR/Module.h"
#include "llvm/IR/PassManager.h"
#include "llvm/Passes/PassBuilder.h"

using namespace llvm;

namespace seapp {

// Run SeaHorn's InstCombine (with the Avoid* knobs, defaulting to SeaHorn
// behavior) over the whole module via the new pass manager.
void runSeaInstCombine(Module &m) {
  PassBuilder PB;
  LoopAnalysisManager LAM;
  FunctionAnalysisManager FAM;
  CGSCCAnalysisManager CGAM;
  ModuleAnalysisManager MAM;
  PB.registerModuleAnalyses(MAM);
  PB.registerCGSCCAnalyses(CGAM);
  PB.registerFunctionAnalyses(FAM);
  PB.registerLoopAnalyses(LAM);
  PB.crossRegisterProxies(LAM, FAM, CGAM, MAM);

  ModulePassManager MPM;
  MPM.addPass(
      createModuleToFunctionPassAdaptor(llvm_seahorn::SeaInstCombinePass()));
  MPM.run(m, MAM);
}

} // namespace seapp
