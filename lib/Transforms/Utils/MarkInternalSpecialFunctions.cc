#include "llvm/ADT/SmallSet.h"
#include "llvm/Analysis/MemoryBuiltins.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"
#include "boost/range.hpp"

#include "seahorn/config.h"

#include "llvm/Analysis/CallGraphSCCPass.h"

using namespace llvm;

namespace seahorn {

/// Mark all functions that allocate or deallocate memory with
/// AlwaysInline attribute
struct MarkInternalAllocOrDeallocInline : public ModulePass {
  static char ID;
  MarkInternalAllocOrDeallocInline() : ModulePass(ID) {}

  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.setPreservesAll();
    AU.addRequired<llvm::TargetLibraryInfoWrapperPass>();
  }

  virtual StringRef getPassName() const {
    return "Mark function that allocate or deallocate memory with AlwaysInline "
           "attribute";
  }

  // Mark any function that has a call to a malloc-like or free-like
  // function. This is actually too conservative.
  bool markIfAllocationFn(Function &F, const TargetLibraryInfo *TLI) {
    for (inst_iterator i = inst_begin(F), e = inst_end(F); i != e; ++i) {
      Instruction *I = &*i;
      if (CallInst *CI = dyn_cast<CallInst>(I)) {
        if (isAllocationFn(CI, TLI, true) || isFreeCall(CI, TLI)) {
          F.addFnAttr(Attribute::AlwaysInline);
          LOG("inline", errs() << "INLINED FUNCTION (DE)ALLOCATING MEMORY "
                               << F.getName() << "\n");
          return true;
        }
      }
    }
    return false;
  }

  bool runOnModule(Module &M) {
    if (M.empty())
      return false;

    bool Change = false;
    // Mark any function that calls a function that (de)allocates
    // memory.
   for (Function &F : M) 
      if (!F.isDeclaration() && F.hasLocalLinkage()) {
        auto &tli = getAnalysis<TargetLibraryInfoWrapperPass>().getTLI(F);
        Change |= markIfAllocationFn(F, &tli);
      }
    return Change;
  }
};

/// Mark C++ constructors or destructors with AlwaysInline attribute
class MarkInternalConstructOrDestructInline : public ModulePass {

private:
  bool isConstructor(Function &F) {
    auto SplitName = F.getName().split("C2");
    return (SplitName.first != "" && SplitName.second != "");
  }

  bool isDestructor(Function &F) {
    auto SplitName = F.getName().split("D2");
    return (SplitName.first != "" && SplitName.second != "");
  }

public:
  static char ID;
  MarkInternalConstructOrDestructInline() : ModulePass(ID) {}

  virtual StringRef getPassName() const {
    return "Mark C++ constructors/destructors with AlwaysInline attribute";
  }

  void getAnalysisUsage(AnalysisUsage &AU) const { AU.setPreservesAll(); }

  bool runOnModule(Module &M) {
    bool Change = false;
    for (Function &F : M) {
      if (!F.isDeclaration() && F.hasLocalLinkage()) {
        if (isConstructor(F) && !F.hasFnAttribute(Attribute::NoInline)) {
          LOG("inline", errs()
                            << "INLINED CONSTRUCTOR " << F.getName() << "\n");
          F.addFnAttr(Attribute::AlwaysInline);
          Change = true;
        } else if (isDestructor(F) && !F.hasFnAttribute(Attribute::NoInline)) {
          LOG("inline", errs() << "INLINED DESTRUCTOR " << F.getName() << "\n");
          F.addFnAttr(Attribute::AlwaysInline);
          Change = true;
        }
      }
    }
    return Change;
  }
};

char MarkInternalAllocOrDeallocInline::ID = 0;

Pass *createMarkInternalAllocOrDeallocInlinePass() {
  return new MarkInternalAllocOrDeallocInline();
}

char MarkInternalConstructOrDestructInline::ID = 0;

Pass *createMarkInternalConstructOrDestructInlinePass() {
  return new MarkInternalConstructOrDestructInline();
}

} // namespace seahorn
