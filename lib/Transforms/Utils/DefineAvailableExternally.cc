/// Turn available_externally function definitions into linkonce_odr ones.
///
/// An available_externally function has a body, but the body is only a copy
/// of a definition that lives in another module. C++ extern templates produce
/// them: libstdc++ declares `extern template class basic_string<char>`, so
/// every std::string member a TU uses is available_externally. InternalizePass
/// keeps such functions as they are, and MarkInternalInlinePass marks only
/// internal functions, so --horn-inline-all leaves calls to them in place.
///
/// The body is the ODR-equivalent definition of the function, so making it
/// the module's own definition (linkonce_odr) does not change the program.
/// InternalizePass, which runs next in seapp, then makes it internal like
/// any other definition. Global variables are not changed (see
/// docs/sea-mlir-export.md).
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/SeaNewPmPasses.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/Stats.hh"

using namespace llvm;

PreservedAnalyses
seahorn::DefineAvailableExternallyPass::run(Module &M,
                                            ModuleAnalysisManager &) {
  bool Changed = false;
  for (Function &F : M) {
    if (F.isDeclaration() || !F.hasAvailableExternallyLinkage())
      continue;
    LOG("avail-ext", errs() << "available_externally to linkonce_odr: "
                            << F.getName() << "\n");
    F.setLinkage(GlobalValue::LinkOnceODRLinkage);
    Stats::count("pp.avail-ext.defined");
    Changed = true;
  }
  return Changed ? PreservedAnalyses::none() : PreservedAnalyses::all();
}
