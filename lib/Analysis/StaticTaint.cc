/*
 * Collecing static Taint Analysis
 * Limitations: No robust support for complex data structures and arrays
 */

#include "seahorn/Analysis/StaticTaint.hh"

#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
using namespace llvm;

namespace seahorn {

char StaticTaint::ID = 0;

bool StaticTaint::runOnBasicBlock(BasicBlock &B) {
  for (auto &inst : B) {
    Instruction *I = &inst;
    LOG("taint", errs() << "Processing..."; I->print(errs()); errs() << "\n";);
    if (CallInst *CI = dyn_cast<CallInst>(I)) {
      Function *f = CI->getCalledFunction();
      if (!f) {
        f = dyn_cast<Function>(CI->getCalledValue()->stripPointerCasts());
      }

      if (!f) {
        WARN << "Skipping indirect call: " << inst;
        continue;
      }
      StringRef funcName = f->getName();
      LOG("taint", errs() << "Function name: " << funcName << "\n";);
      if (funcName.contains("spec_user")) {
        Value *op = CI->getOperand(0);
        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(op))
          op = GEP->getPointerOperand();
        m_taint.insert(op);
      }
    } else if (BranchInst *BI = dyn_cast<BranchInst>(I)) {
      if (BI->isConditional()) {
        Value *cond = BI->getCondition();
        if (m_taint.find(cond) != m_taint.end()) {
          m_taint.insert(BI);
          return true;
        }
      }
    } else {
      if (LoadInst *LI = dyn_cast<LoadInst>(I)) {
        Value *ptr = LI->getPointerOperand();
        if (m_taint.find(ptr) != m_taint.end())
          m_taint.insert(I);
      } else if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(I)) {
        Value *ptr = GEP->getPointerOperand();
        if (m_taint.find(ptr) != m_taint.end())
          m_taint.insert(I);
      } else if (StoreInst *SI = dyn_cast<StoreInst>(I)) {

      } else {
        for (Use &U : I->operands()) {
          Value *v = U.get();
          if (m_taint.find(v) != m_taint.end() &&
              !v->getType()->isPointerTy()) {
            m_taint.insert(I);
            break;
          }
        }
      }
    }
  }
  return false;
}

void StaticTaint::taintBB(BasicBlock &B) {
  for (auto &inst : B)
    m_taint.insert(&inst);
}

void StaticTaint::runOnFunction(Function &F) {
  if (F.isDeclaration())
    return;

  m_dm.recalculate(F);

  BasicBlock *taintedBB = nullptr;
  for (auto &B : F) {
    if (taintedBB && m_dm.dominates(&B, taintedBB))
      taintedBB = nullptr;

    if (!taintedBB) {
      bool branchTainted = runOnBasicBlock(B);
      if (branchTainted && !taintedBB)
        taintedBB = &B;
    } else {
      taintBB(B);
    }
  }
}

bool StaticTaint::runOnModule(llvm::Module &M) {
  if (M.begin() == M.end())
    return false;

  LOG("taint", M.print(errs(), nullptr););
  for (Function &F : M) {
    runOnFunction(F);
  }

  return false;
}

void StaticTaint::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

} // namespace seahorn

namespace seahorn {
llvm::Pass *createStaticTaintPass() { return new StaticTaint(); }
} // namespace seahorn

static llvm::RegisterPass<seahorn::StaticTaint> X("static-taint-analysis",
                                                  "Static-Taint Analysis");
