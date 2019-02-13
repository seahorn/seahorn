/*
 * Collecing static Taint Analysis
 * Limitations: No robust support for complex data structures and arrays
 */

#include "seahorn/Analysis/StaticTaint.hh"

#include "llvm/CodeGen/MachineDominators.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Support/Debug.h"
#include "llvm/IR/DebugInfoMetadata.h"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include <deque>

using namespace llvm;

namespace seahorn {

char StaticTaint::ID = 0;

bool StaticTaint::runOnBasicBlock(BasicBlock &B) {
  for (auto &inst : B) {
    Instruction *I = &inst;
    if (m_taint.find(I) != m_taint.end()) continue;
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
      if (funcName.contains("__taint")) {
        Value *op = CI->getOperand(0);
        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(op))
          op = GEP->getPointerOperand();
        m_taint.insert(op);
      }
      else if (funcName.contains("__is_tainted")) {
        Value *op = CI->getOperand(0);
        if (GetElementPtrInst *GEP = dyn_cast<GetElementPtrInst>(op))
          op = GEP->getPointerOperand();
        if (isTainted(op)) {
          m_tainted.insert(CI);
        }
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
        /*Value *ptr = SI->getPointerOperand();
        Value *src = SI->getOperand(0);
        if (m_taint.find(src) != m_taint.end())
          m_taint.insert(ptr);
        else
          m_taint.erase(ptr);*/
      } else if (PHINode *PHI = dyn_cast<PHINode>(I)) {
        PHINode::value_op_iterator it = PHI->value_op_begin();
        PHINode::value_op_iterator end = PHI->value_op_end();
        for (; it != end; it++) {
          Value *v = *it;
          if (m_taint.find(v) != m_taint.end()) {
            LOG("taint", errs() << "Tainting..."; I->print(errs()); errs() << "\n";);
            m_taint.insert(I);
            break;
          }
        }
      } else {
        for (Use &U : I->operands()) {
          Value *v = U.get();
          if (m_taint.find(v) != m_taint.end() &&
              !v->getType()->isPointerTy()) {
            LOG("taint", errs() << "Tainting..."; I->print(errs()); errs() << "\n";);
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
  for (auto &inst : B) {
	LOG("taint", errs() << "Tainting..."; inst.print(errs()); errs() << "\n";);
    m_taint.insert(&inst);
  }
}

void StaticTaint::runOnFunction(Function &F) {
  if (F.isDeclaration())
    return;

  m_dm.recalculate(F);
  std::deque<BasicBlock*> WorkList;
  for (auto &B : F) WorkList.push_back(&B);

  BasicBlock *taintedBB = nullptr;
  while(!WorkList.empty()) {
	BasicBlock &B = *(WorkList.front());
	WorkList.pop_front();
	BranchInst *Br = dyn_cast<BranchInst>(B.getTerminator());

    if (taintedBB && m_dm.dominates(&B, taintedBB))
      taintedBB = nullptr;

    unsigned before = m_taint.size();
    if (!taintedBB) {
      bool branchTainted = runOnBasicBlock(B);
      if (branchTainted && !taintedBB)
        taintedBB = &B;
    } else {
      taintBB(B);
    }


    /// XXX Currently we may add BBs that are already scheduled to be
    /// XXX processed. Should avoid this when possible
    if (Br != nullptr && before < m_taint.size()) {
      if (Br->isConditional()) {
        WorkList.push_back(cast<BasicBlock>(Br->getOperand(1)));
        WorkList.push_back(cast<BasicBlock>(Br->getOperand(2)));
      } else {
        WorkList.push_back(cast<BasicBlock>(Br->getOperand(0)));
      }
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

  if (m_bPrintAnalysis) {
    outs() << "\n==================== TAINT ANALYSIS ====================\n";
    for (CallInst * CI : m_tainted) {
      outs() << "Tainted expression found at: ";
      DILocation *loc = CI->getDebugLoc().get();
      if (loc != nullptr) {
        outs() << loc->getFilename().str() << " line: " << loc->getLine();
      }
      else outs() << "-- No Debug Info";
      outs() << "\n";
    }
    outs() << "\n========================== END =========================\n";
  }

  return false;
}

void StaticTaint::getAnalysisUsage(llvm::AnalysisUsage &AU) const {
  AU.setPreservesAll();
}

} // namespace seahorn

namespace seahorn {
llvm::Pass *createStaticTaintPass(bool bPrint = false) { return new StaticTaint(bPrint); }
} // namespace seahorn

static llvm::RegisterPass<seahorn::StaticTaint> X("static-taint-analysis",
                                                  "Static-Taint Analysis");
