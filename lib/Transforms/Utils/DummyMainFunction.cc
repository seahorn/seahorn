/** Insert dummy main function if one does not exist */

#include "llvm/Analysis/OptimizationRemarkEmitter.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Type.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Debug.h"
#include "llvm/Support/raw_ostream.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

using namespace llvm;

#define DEBUG_TYPE "sea-dummy-main"

static llvm::cl::opt<std::string>
    EntryPoint("entry-point",
               llvm::cl::desc("Set Entry point to be other than main."),
               llvm::cl::init(""));

namespace seahorn {

class DummyMainFunction : public ModulePass {
  DenseMap<const Type *, FunctionCallee> m_ndfn;

  FunctionCallee makeNewNondetFn(Module &m, Type &type, unsigned num,
                                 std::string prefix) {
    std::string name;
    unsigned c = num;
    do {
      name = prefix + std::to_string(c++);
    } while (m.getNamedValue(name));
    FunctionCallee res = m.getOrInsertFunction(name, &type);
    return res;
  }

  FunctionCallee getNondetFn(Type *type, Module &M) {
    auto it = m_ndfn.find(type);
    if (it != m_ndfn.end()) {
      return it->second;
    }

    FunctionCallee res =
        makeNewNondetFn(M, *type, m_ndfn.size(), "verifier.nondet.");
    m_ndfn[type] = res;
    return res;
  }

public:
  static char ID;

  DummyMainFunction() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {
    if (EntryPoint != "" && M.getFunction("main")) {
      std::unique_ptr<OptimizationRemarkEmitter> OwnedORE =
          std::make_unique<OptimizationRemarkEmitter>(M.getFunction("main"));
      OptimizationRemarkEmitter *ORE = OwnedORE.get();

      LOG("dummy-main",
          WARN << "DummyMainFunction: Main already exists. Deleting it!\n");
      // NOTE: assuming no uses of main
      ORE->emit(
          OptimizationRemark(DEBUG_TYPE, "ReplaceMain", M.getFunction("main"))
          << " Will replace main function with entry to (in-order) "
          << EntryPoint);
      M.getFunction("main")->eraseFromParent();
    }

    Function *Entry = nullptr;
    if (EntryPoint != "")
      Entry = M.getFunction(EntryPoint);

    // --- Create main
    LLVMContext &ctx = M.getContext();
    Type *intTy = Type::getInt32Ty(ctx);

    ArrayRef<Type *> params;
    Function *main = Function::Create(
        FunctionType::get(intTy, params, false),
        GlobalValue::LinkageTypes::ExternalLinkage, "main", &M);

    IRBuilder<> B(ctx);
    BasicBlock *BB = BasicBlock::Create(ctx, "", main);
    B.SetInsertPoint(BB, BB->begin());

    std::vector<Function *> FunctionsToCall;
    if (Entry) {
      FunctionsToCall.push_back(Entry);
    } else {
      // --- if no selected entry found then we call to all
      //     non-declaration functions.
      for (auto &F : M) {
        if (F.getName() == "main") // avoid recursive call to main
          continue;
        if (F.isDeclaration())
          continue;
        FunctionsToCall.push_back(&F);
      }
    }

    for (auto F : FunctionsToCall) {
      // -- create a call with non-deterministic actual parameters
      SmallVector<Value *, 16> Args;
      for (auto &A : F->args()) {
        FunctionCallee ndf = getNondetFn(A.getType(), M);
        Args.push_back(B.CreateCall(ndf));
      }
      CallInst *CI = B.CreateCall(F, Args);
      LOG("dummy-main",
          errs() << "DummyMainFunction: created a call " << *CI << "\n");
    }

    // -- return of main
    // our favourite exit code
    B.CreateRet(ConstantInt::get(intTy, 42));

    // GlobalVariable *LLVMUsed = M.getGlobalVariable("llvm.used");
    // std::vector<Constant*> MergedVars;
    // if (LLVMUsed) {
    //   // Collect the existing members of llvm.used
    //   ConstantArray *Inits = cast<ConstantArray>(LLVMUsed->getInitializer());
    //   for (unsigned I = 0, E = Inits->getNumOperands(); I != E; ++I) {
    //     Value* V = Inits->getOperand(I)->stripPointerCasts();
    //     MergedVars.push_back(Inits->getOperand(I));
    //   }
    //   LLVMUsed->eraseFromParent();
    // }

    // Type *i8PTy = Type::getInt8PtrTy(ctx);
    // // Add uses for our data
    // //MergedVars.push_back (ConstantExpr::getBitCast(cast<llvm::Constant>(F),
    // i8PTy));
    // // XXX: this shouldn't be necessary but for some reason DCE
    // //       does not like my main and deletes it
    // MergedVars.push_back
    // (ConstantExpr::getBitCast(cast<llvm::Constant>(main), i8PTy));

    // // Recreate llvm.used.
    // ArrayType *ATy = ArrayType::get(i8PTy, MergedVars.size());
    // LLVMUsed = new llvm::GlobalVariable(
    //     M, ATy, false, llvm::GlobalValue::AppendingLinkage,
    //     llvm::ConstantArray::get(ATy, MergedVars), "llvm.used");
    // LLVMUsed->setSection("llvm.metadata");

    return true;
  }

  void getAnalysisUsage(AnalysisUsage &AU) const override {
    AU.setPreservesAll();
  }

  virtual StringRef getPassName() const override {
    return "Add dummy main function";
  }
};

char DummyMainFunction::ID = 0;

Pass *createDummyMainFunctionPass() { return new DummyMainFunction(); }

} // namespace seahorn
