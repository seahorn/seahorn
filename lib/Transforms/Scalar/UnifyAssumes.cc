#include "llvm/Analysis/AssumptionCache.h"
#include "llvm/Analysis/CallGraph.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Dominators.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"
#include "llvm/Support/CommandLine.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"
#include "llvm/Transforms/Utils/PromoteMemToReg.h"
#include "llvm/Transforms/Utils/UnifyFunctionExitNodes.h"

#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
using namespace llvm;

static cl::opt<bool> EnableDae(
    "enable-dae",
    cl::desc("Enabled eliminating dead asserts, i.e.,  verifier.assert(true)"),
    cl::init(false));

static cl::opt<bool>
    RMUnifiedAssumes("remove-unified-assumes",
                     cl::desc("Deleting verifier.assume calls"),
                     cl::init(true));

namespace {
class UnifyAssumesPass : public ModulePass {

private:
  seahorn::SeaBuiltinsInfo *m_SBI;

public:
  static char ID;
  static llvm::StringRef s_assumeUnifiedTag;
  UnifyAssumesPass() : ModulePass(ID) {}

  bool runOnModule(Module &M) override {
    Function *main = M.getFunction("main");
    if (main)
      return runOnFunction(*main);
    return false;
  }

  bool runOnFunction(Function &F);

  void processCallInst(CallInst &CI, AllocaInst &flag);
  void processAssertInst(CallInst &CI, AllocaInst &flag);
  bool isAssumeCall(const CallInst &ci);
  bool isAssertCall(const CallInst &ci);
  CallInst *findSeahornFail(llvm::Function &F);
  void markAssumeAsUnified(CallInst &CI);
  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<seahorn::SeaBuiltinsInfoWrapperPass>();
    AU.addRequired<llvm::CallGraphWrapperPass>();
    AU.addRequired<llvm::DominatorTreeWrapperPass>();
    AU.addRequired<llvm::AssumptionCacheTracker>();
    // XXX breaks call graph
    AU.setPreservesAll();
  }

  llvm::StringRef getPassName() const override { return "UnifyAssumesPass"; }
};

char UnifyAssumesPass::ID = 0;
llvm::StringRef UnifyAssumesPass::s_assumeUnifiedTag = "unified.assume";

bool UnifyAssumesPass::isAssumeCall(const CallInst &ci) {
  using namespace seahorn;
  switch (m_SBI->getSeaBuiltinOp(ci)) {
  default:
    return false;
  case SeaBuiltinsOp::ASSUME:
  case SeaBuiltinsOp::ASSUME_NOT:
    return true;
  }
}

bool UnifyAssumesPass::isAssertCall(const CallInst &ci) {
  using namespace seahorn;
  switch (m_SBI->getSeaBuiltinOp(ci)) {
  default:
    return false;
  case SeaBuiltinsOp::ASSERT:
  case SeaBuiltinsOp::ASSERT_NOT:
    return true;
  }
}

/// Find a function exit basic block.  Assumes that the function has
/// a unique block with return instruction
llvm::BasicBlock *findExitBlock(llvm::Function &F) {
  for (llvm::BasicBlock &bb : F)
    if (llvm::isa<llvm::ReturnInst>(bb.getTerminator()))
      return &bb;
  return nullptr;
}

CallInst *UnifyAssumesPass::findSeahornFail(llvm::Function &F) {
  for (auto &inst : instructions(F)) {
    if (auto *CI = dyn_cast<CallInst>(&inst)) {
      if (m_SBI->getSeaBuiltinOp(*CI) == seahorn::SeaBuiltinsOp::FAIL)
        return CI;
    }
  }
  return nullptr;
}

bool UnifyAssumesPass::runOnFunction(Function &F) {
  Module &M = *F.getParent();
  m_SBI = &getAnalysis<seahorn::SeaBuiltinsInfoWrapperPass>().getSBI();
  auto *assumeFn = m_SBI->mkSeaBuiltinFn(seahorn::SeaBuiltinsOp::ASSUME, M);

  SmallVector<CallInst *, 16> assumes;
  SmallVector<CallInst *, 16> asserts;
  for (auto &inst : instructions(F)) {
    if (auto *ci = dyn_cast<CallInst>(&inst)) {
      if (isAssumeCall(*ci)) {
        assumes.push_back(ci);
      } else if (isAssertCall(*ci)) {
        asserts.push_back(ci);
      }
    }
  }
  if (assumes.empty()) {
    return false;
  }

  // -- make sure there is an exit block to insert the final assume
  BasicBlock *exitBlock = findExitBlock(F);
  if (!exitBlock) {
    WARN << "Assumes not unified. No return found in `main`";
    return false;
  }

  BasicBlock &entryBB = F.getEntryBlock();
  IRBuilder<> B(&entryBB, entryBB.begin());
  AllocaInst *assumeFlag;
  // -- generate code to allocate and initialize assumeFlag
  assumeFlag = B.CreateAlloca(B.getInt1Ty(), 0U, nullptr, "assume.flag");
  B.CreateStore(B.getTrue(), assumeFlag);

  // -- process all assumes
  for (auto ci : assumes) {
    processCallInst(*ci, *assumeFlag);
  }

  // -- delete all assumes or
  // -- distinguish assume by metadata
  for (auto ci : assumes) {
    if (!RMUnifiedAssumes)
      markAssumeAsUnified(*ci);
    else
      ci->eraseFromParent();
  }

  // -- process all asserts
  for (auto ci : asserts) {
    processAssertInst(*ci, *assumeFlag);
  }

  // -- cleanup the asserts vector
  asserts.clear();

  // insert call to assume before the last instructions of the exit block
  // (maybe before seahorn.fail)
  CallInst *seaFailCall = findSeahornFail(F);
  if (seaFailCall) {
    B.SetInsertPoint(seaFailCall);
  } else {
    B.SetInsertPoint(exitBlock->getTerminator());
  }
  B.CreateCall(assumeFn, B.CreateLoad(assumeFlag));

  LOG("unify.dump", errs() << F << "\n";);

  // -- run mem2reg to lower assumeFlag to register
  DominatorTree &DT =
      getAnalysis<llvm::DominatorTreeWrapperPass>(F).getDomTree();
  AssumptionCache &AC =
      getAnalysis<llvm::AssumptionCacheTracker>().getAssumptionCache(F);
  PromoteMemToReg(assumeFlag, DT, &AC);

  return false;
}

void UnifyAssumesPass::markAssumeAsUnified(CallInst &CI) {
  MDNode *meta = MDNode::get(CI.getContext(), None);
  CI.setMetadata(s_assumeUnifiedTag, meta);
}

void UnifyAssumesPass::processAssertInst(CallInst &CI, AllocaInst &flag) {
  BasicBlock *bb = CI.getParent();
  Module *M = bb->getParent()->getParent();
  assert(bb);
  assert(M);

  llvm::CallSite CS(&CI);
  IRBuilder<> B(bb);
  B.SetInsertPoint(&CI);
  Value *conseq = CS.getArgument(0);
  // remove instruction if verifier.assert(true)
  if (EnableDae) {
    if (auto *conseq_const = dyn_cast<llvm::ConstantInt>(conseq)) {
      if (!conseq_const->isZero()) {
        CI.eraseFromParent();
        return;
      }
    }
  }
  auto ante = B.CreateLoad(&flag);
  // negate condition if verifier.assert.not seen
  bool isNot = m_SBI->getSeaBuiltinOp(CI) == seahorn::SeaBuiltinsOp::ASSERT_NOT;
  if (isNot) {
    conseq = B.CreateNot(conseq);
  }
  // transform verifier.assert(cond) into sea.assert.if(flag, cond)
  Function *assertIfFn =
      m_SBI->mkSeaBuiltinFn(seahorn::SeaBuiltinsOp::ASSERT_IF, *M);
  CallInst *NewCI = CallInst::Create(assertIfFn, {ante, conseq});
  NewCI->setCallingConv(assertIfFn->getCallingConv());
  NewCI->copyMetadata(CI);
  if (!CI.use_empty())
    CI.replaceAllUsesWith(NewCI);
  ReplaceInstWithInst(&CI, NewCI);
  return;
}

void UnifyAssumesPass::processCallInst(CallInst &CI, AllocaInst &flag) {
  BasicBlock *bb = CI.getParent();
  assert(bb);

  IRBuilder<> B(bb);
  B.SetInsertPoint(&CI);

  bool isNot = CI.getCalledFunction()->getName().equals("verifier.assume.not");
  llvm::CallSite CS(&CI);

  Value *cond = CS.getArgument(0);
  if (isNot)
    cond = B.CreateNot(cond);

  // transform verifier.assume(cond) into flag := flag && cond
  B.CreateStore(B.CreateAnd(B.CreateLoad(&flag), cond), &flag);
  return;
}
} // namespace

namespace seahorn {
Pass *createUnifyAssumesPass() { return new UnifyAssumesPass(); };
bool isUnifiedAssume(const Instruction &I) {
  return I.hasMetadata(UnifyAssumesPass::s_assumeUnifiedTag);
}
} // namespace seahorn
