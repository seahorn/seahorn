#include "seahorn/Transforms/Instrumentation/GeneratePartialFnPass.hh"

#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/InitializePasses.hh"
#include "seahorn/Passes.hh"
#include "seahorn/Support/SeaDebug.h"

#include "llvm_seahorn/IR/LLVMContext.h"
#include "llvm/IR/Constants.h"
#include "llvm/IR/IRBuilder.h"

#define PARTIAL_FN_ANNOTATION "partial"
#define PARTIAL_FN_STUB_PREFIX "sea.synth.inferable."

#define PASS_NAME "generate-partial-fn"
#define DEBUG_TYPE PASS_NAME

using namespace llvm;

namespace {

// Returns true if I is marked by the "partial" metadata.
bool hasPartialAnnotation(const llvm::Instruction &I) {
  if (auto *meta = I.getMetadata(llvm_seahorn::LLVMContext::MD_annotation)) {
    auto *tuple = cast<MDTuple>(meta);
    for (auto &N : tuple->operands()) {
      if (cast<MDString>(N.get())->getString() == PARTIAL_FN_ANNOTATION) {
        return true;
      }
    }
  }
  return false;
}

} // namespace

namespace seahorn {

// Delcared in GeneratePartialFnPass.h
bool isInferable(const Function &F) {
  return F.getName().startswith(PARTIAL_FN_STUB_PREFIX);
}

// Delcared in GeneratePartialFnPass.h
bool isPartialFn(const Function &F) {
  // Conservative check: Is the first instruction marked as partial?
  if (!F.empty()) {
    auto &I = F.getEntryBlock().front();
    return hasPartialAnnotation(I);
  }
  return false;
}

namespace {

// Instruments partial functions. This consists of identifying partial functions
// (Boolean functions annotated with partial), locating all stubs (external
// functions called from within the partial function), and instrumenting all
// stubs as required in VC generations.
class GeneratePartialFnPass : public llvm::ModulePass {
private:
  Function *m_assumeFn = nullptr;

public:
  static char ID;

  GeneratePartialFnPass() : ModulePass(ID) {}

  virtual void getAnalysisUsage(llvm::AnalysisUsage &AU) const {
    AU.addRequired<SeaBuiltinsInfoWrapperPass>();
    AU.setPreservesAll();
  }

  bool runOnModule(Module &M) {
    auto &SBI = getAnalysis<SeaBuiltinsInfoWrapperPass>().getSBI();
    m_assumeFn = SBI.mkSeaBuiltinFn(SeaBuiltinsOp::ASSUME, M);

    bool changed = false;
    for (auto &F : M) {
      if (!F.empty()) {
        changed |= runOnFunction(SBI, F);
      }
    }
    return changed;
  }

  bool runOnFunction(SeaBuiltinsInfo &SBI, Function &F) {
    // Checks that this is a partial function, with a Boolean return type.
    if (!isPartialFn(F))
      return false;

    if (!F.getReturnType()->isIntegerTy(1)) {
      DOG(errs() << "Partial function without Bool return type: "
                 << F.getName().str() << "\n";);
      return false;
    }

    // Provides a placeholder implementation to each partial function stub.
    bool changed = false;
    for (auto &BB : F) {
      IRBuilder<> pfnBuilder(&BB);

      for (auto &I : BB) {
        // Does I call a user defined function.
        CallBase *CB = dyn_cast<CallBase>(&I);
        if (!CB || SBI.isSeaBuiltin(*CB))
          continue;

        // Is the callee defined.
        Function *CF = CB->getCalledFunction();
        if (!CF || !CF->isDeclaration())
          continue;

        // Does the function return an integer?
        if (!CF->getReturnType() || !CF->getReturnType()->isIntegerTy())
          continue;

        // Records changes.
        changed = true;
        DOG(errs() << "Found external call from partial function "
                   << F.getName().str() << " to " << CF->getName().str()
                   << ".\n");

        // Renames the stub so that it can be identified in other passes.
        CF->setName(PARTIAL_FN_STUB_PREFIX + CF->getName().str());

        // The stub should have a body. The body will force the ModuleHornify
        // pass to generate a call to the stub. Consequently, arguments passed
        // to the stub will be live within the partial function that calls it.
        BasicBlock *block = BasicBlock::Create(CF->getContext(), "entry", CF);
        IRBuilder<> stubBuilder(block);
        stubBuilder.CreateRet(ConstantInt::get(CF->getReturnType(), 0));

        // Ensures that the stub is not optimized away by sequential LLVM
        // passes.
        CF->addFnAttr(Attribute::NoInline);
        CF->addFnAttr(Attribute::OptimizeNone);

        // Within the partial function, assume that the call to the stub never
        // happens. This allows for the body to be synthesized, starting from
        // the location of the call.
        pfnBuilder.SetInsertPoint(&I);
        pfnBuilder.CreateCall(m_assumeFn, pfnBuilder.getFalse());
      }
    }
    return changed;
  }

  virtual StringRef getPassName() const { return PASS_NAME; }
};

char GeneratePartialFnPass::ID = 0;

} // namespace

llvm::Pass *createGeneratePartialFnPass() {
  return new GeneratePartialFnPass();
}

} // namespace seahorn

using namespace seahorn;
INITIALIZE_PASS(GeneratePartialFnPass, PASS_NAME,
                "Marks and instruments partial function stubs.", false, false)
