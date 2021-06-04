#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include "boost/range.hpp"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Transforms/Instrumentation/GeneratePartialFnPass.hh"

using namespace llvm;

static llvm::cl::list<std::string>
    InlineOnly("horn-inline-only",
               llvm::cl::desc("Inline only selected functions"),
               llvm::cl::ZeroOrMore, llvm::cl::CommaSeparated);

namespace seahorn {

/// marks all internal functions with AlwaysInline attribute
struct MarkInternalInline : public ModulePass {
  static char ID;
  MarkInternalInline() : ModulePass(ID) {}

  virtual StringRef getPassName() const {
    return "Mark all internal functions with AlwaysInline attribute";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const { AU.setPreservesAll(); }

  bool runOnModule(Module &M) {
    SmallSet<Function *, 8> selectedFn;
    for (auto &fname :
         boost::make_iterator_range(InlineOnly.begin(), InlineOnly.end()))
      if (Function *F = M.getFunction(fname))
        selectedFn.insert(F);

    for (Function &F : M) {
      if (!F.isDeclaration() && F.hasLocalLinkage()) {
        if (selectedFn.empty() || selectedFn.count(&F) > 0) {
          if (!isPartialFn(F)) {
            LOG("inline", errs() << "INLINED " << F.getName() << "\n");

            if (F.hasFnAttribute(Attribute::NoInline)) {
              F.removeFnAttr(Attribute::NoInline);
            }
            F.addFnAttr(Attribute::AlwaysInline);
          } else {
            LOG("inline",
                errs() << "Did not inline partial fn: " << F.getName() << "\n");
          }
        }
      }
    }
    return true;
  }
};

char MarkInternalInline::ID = 0;

Pass *createMarkInternalInlinePass() { return new MarkInternalInline(); }

} // namespace seahorn
