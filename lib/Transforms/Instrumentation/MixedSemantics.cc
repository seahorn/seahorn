#include "seahorn/Transforms/Instrumentation/MixedSemantics.hh"
#include "seahorn/Analysis/CanFail.hh"
#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Transforms/Scalar/PromoteVerifierCalls.hh"
#include "seahorn/Transforms/Utils/Local.hh"

#include "llvm/ADT/PostOrderIterator.h"
#include "llvm/ADT/SCCIterator.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/CFG.h"
#include "llvm/IR/GlobalValue.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Scalar.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/Cloning.h"
#include "llvm/Transforms/Utils/Local.h"

#include "boost/range.hpp"
#include "seahorn/Support/SeaDebug.h"

static llvm::cl::opt<bool>
    ReduceMain("ms-reduce-main", llvm::cl::desc("Reduce main to return paths"),
               llvm::cl::init(false));

static llvm::cl::opt<bool> KeepOrigMain(
    "keep-orig-main",
    llvm::cl::desc("Keep original main() function under main.orig() name"),
    llvm::cl::init(false));

namespace seahorn {
using namespace llvm;

char MixedSemantics::ID = 0;

static void removeError(Function &F, SeaBuiltinsInfo &SBI) {
  for (auto &BB : F) {
    for (auto &I : BB) {
      CallInst *ci = dyn_cast<CallInst>(&I);
      if (!ci)
        continue;
      Function *cf = ci->getCalledFunction();
      if (!cf)
        continue;
      if (!cf->getName().equals("verifier.error"))
        continue;

      auto *assumeFn =
          SBI.mkSeaBuiltinFn(SeaBuiltinsOp::ASSUME, *F.getParent());
      ReplaceInstWithInst(ci, CallInst::Create(assumeFn, ConstantInt::getFalse(
                                                             F.getContext())));
      // does not matter what verifier.error() call is followed by in this bb
      break;
    }
  }
}

static bool ExternalizeDeclarations(Module &M) {
  bool change = false;
  for (Module::iterator I = M.begin(), E = M.end(); I != E;) {
    Function &F = *I++;
    if (F.isDeclaration() &&
        (F.getLinkage() == GlobalValue::LinkageTypes::InternalLinkage)) {
      F.setLinkage(GlobalValue::LinkageTypes::ExternalLinkage);
      change = true;
    }
  }
  return change;
}

// If the function becomes empty then it cannot have metadata in its
// declaration.
static void removeMetadataIfFunctionIsEmpty(Function &f) {
  if (f.empty() && f.hasMetadata())
    f.clearMetadata();
}

bool MixedSemantics::runOnModule(Module &M) {
  LOG("mixed-sem", errs() << "Starting MixedSemantics\n";);
  Function *main = M.getFunction("main");
  if (!main)
    return false;

  removeUnreachableBlocks(*main);

  auto &SBI = getAnalysis<SeaBuiltinsInfoWrapperPass>().getSBI();

  CanFail &CF = getAnalysis<CanFail>();
  if (!CF.canFail(main)) {
    LOG("mixed-sem", errs() << "main() cannot fail\n";);
    // -- this benefits the legacy front-end.
    // -- it might create issues in some applications where mixed-semantics is
    // applied
    if (ReduceMain)
      reduceToReturnPaths(*main, SBI);
    removeMetadataIfFunctionIsEmpty(*main);
    return false;
  }
  LOG("mixed-sem", errs() << "main() can fail, reducing\n";);

  main->setName("orig.main");
  FunctionType *mainTy = main->getFunctionType();
  FunctionType *newTy = FunctionType::get(
      Type::getInt32Ty(M.getContext()),
      ArrayRef<Type *>(mainTy->param_begin(), mainTy->param_end()), false);

  Function *newM = Function::Create(newTy, main->getLinkage(), "main", &M);
  newM->copyAttributesFrom(main);

  // -- mark old main as private
  main->setLinkage(GlobalValue::LinkageTypes::PrivateLinkage);

  BasicBlock *entry = BasicBlock::Create(M.getContext(), "entry", newM);

  IRBuilder<> Builder(M.getContext());
  Builder.SetInsertPoint(entry, entry->begin());

  SmallVector<Value *, 16> fargs;
  for (auto &a : newM->args())
    fargs.push_back(&a);

  InlineFunctionInfo IFI;
  CallInst *mcall = Builder.CreateCall(main, fargs);
  Builder.CreateUnreachable();
  InlineFunction(mcall, IFI);

  DenseMap<const Function *, BasicBlock *> entryBlocks;
  DenseMap<const Function *, SmallVector<Value *, 16>> entryPrms;

  SmallVector<BasicBlock *, 4> errBlocks;

  IRBuilder<> enBldr(M.getContext());
  enBldr.SetInsertPoint(entry, entry->begin());

  for (Function &F : M) {
    if (&F == main || &F == newM)
      continue;
    if (!CF.canFail(&F)) {
      if (!F.isDeclaration())
        reduceToReturnPaths(F, SBI);
      continue;
    }

    BasicBlock *bb = BasicBlock::Create(M.getContext(), F.getName(), newM);
    entryBlocks[&F] = bb;

    Builder.SetInsertPoint(bb, bb->begin());

    if (!CF.mustFail(&F)) {
      fargs.clear();
      auto &p = entryPrms[&F];
      for (auto &a : boost::make_iterator_range(F.arg_begin(), F.arg_end())) {
        p.push_back(enBldr.CreateAlloca(a.getType()));
        fargs.push_back(Builder.CreateLoad(p.back()));
      }

      CallInst *fcall = Builder.CreateCall(&F, fargs);
      Builder.CreateUnreachable();
      InlineFunction(fcall, IFI);
      removeError(F, SBI);
      reduceToReturnPaths(F, SBI);
    } else {
      Builder.CreateRet(Builder.getInt32(42));
      errBlocks.push_back(bb);
    }
  }

  std::vector<CallInst *> workList;

  FunctionCallee ndFn =
      M.getOrInsertFunction("nondet.bool", Type::getInt1Ty(M.getContext()));
  for (BasicBlock &BB : *newM) {
    for (auto &I : BB) {
      CallInst *ci = dyn_cast<CallInst>(&I);
      if (!ci)
        continue;
      Function *cf = ci->getCalledFunction();
      if (entryBlocks.count(cf) <= 0)
        continue;
      // -- would create a back-jump
      if (entryBlocks[cf] == &BB)
        continue;
      workList.push_back(ci);
    }
  }

  for (auto *ci : workList) {
    BasicBlock *bb = ci->getParent();
    BasicBlock *post = bb->splitBasicBlock(ci, "postcall");

    bb->getTerminator()->eraseFromParent();
    Builder.SetInsertPoint(bb);

    BranchInst *br;
    if (CF.mustFail(ci->getCalledFunction())) {
      br = Builder.CreateBr(entryBlocks[ci->getCalledFunction()]);
      br->setDebugLoc(ci->getDebugLoc());
      continue;
    }

    BasicBlock *argBb =
        BasicBlock::Create(M.getContext(), "precall", newM, post);
    br = Builder.CreateCondBr(Builder.CreateCall(ndFn), post, argBb);
    br->setDebugLoc(ci->getDebugLoc());

    Builder.SetInsertPoint(argBb);

    CallSite CS(ci);
    auto &params = entryPrms[ci->getCalledFunction()];

    for (unsigned i = 0; i < params.size(); ++i) {
      StoreInst *si = Builder.CreateStore(CS.getArgument(i), params[i]);
      si->setDebugLoc(ci->getDebugLoc());
    }

    br = Builder.CreateBr(entryBlocks[ci->getCalledFunction()]);
    br->setDebugLoc(ci->getDebugLoc());
  }

  AttrBuilder B;

  // --- make sure the optimizer does not remove it
  B.addAttribute(Attribute::OptimizeNone);

  AttributeList as =
      AttributeList::get(M.getContext(), AttributeList::FunctionIndex, B);
  auto failureFn = dyn_cast<Function>(
      M.getOrInsertFunction("seahorn.fail", as, Type::getVoidTy(M.getContext()))
          .getCallee());

  for (auto errB : errBlocks) {
    // --- add placeholder to indicate that the function can fail
    Builder.SetInsertPoint(errB, errB->begin());
    Builder.CreateCall(failureFn);
  }

  reduceToAncestors(
      *newM,
      SmallVector<const BasicBlock *, 4>(errBlocks.begin(), errBlocks.end()),
      SBI);

  ExternalizeDeclarations(M);

  if (!KeepOrigMain)
    main->eraseFromParent();

  return true;
}

void MixedSemantics::getAnalysisUsage(AnalysisUsage &AU) const {
  // XXX Removed since switches are assumed to be removed by pp pipeline
  // AU.addRequiredID (LowerSwitchID);
  AU.addRequired<SeaBuiltinsInfoWrapperPass>();
  AU.addRequired<CallGraphWrapperPass>();
  AU.addRequired<CanFail>();
  AU.addRequired<PromoteVerifierCalls>();
}

} // namespace seahorn

namespace seahorn {
Pass *createMixedSemanticsPass() { return new MixedSemantics(); }
} // namespace seahorn

static llvm::RegisterPass<seahorn::MixedSemantics>
    X("mixed-semantics", "Transform into mixed semantics");
