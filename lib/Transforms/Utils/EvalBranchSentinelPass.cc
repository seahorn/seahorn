#include "seahorn/Analysis/SeaBuiltinsInfo.hh"
#include "seahorn/InitializePasses.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"

#include "llvm/ADT/SmallSet.h"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/DebugInfo.h"
#include "llvm/IR/DebugLoc.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/IR/Instruction.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Value.h"
#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/Transforms/Utils/BasicBlockUtils.h"

#include <fstream>
#include <unordered_set>

using namespace llvm;

/**
 * This pass looks at all branch sentinal instructions inserted by a previous
 * pass and sees if any of them evaluate unambiguously to true or false.
 * It then prints out the debug location of that branch. This is useful since
 * we want to know which conditional branches have become unconditional.
 */
namespace seahorn {
struct EvalBranchSentinelPass : public FunctionPass {
  static char ID;
  seahorn::SeaBuiltinsInfo *m_SBI;
  std::unordered_set<std::string> m_condTrue;
  std::unordered_set<std::string> m_condFalse;
  // TODO: add for inst wo dloc
  std::unordered_set<std::string> m_unlowered;
  llvm::DenseMap<Instruction *, bool> m_unknown;

  EvalBranchSentinelPass() : FunctionPass(ID) {}
  bool isBranchSentinelCall(const CallInst &ci);
  bool runOnFunction(Function &F) override;
  void processSentinels(SmallVector<CallInst *, 16> &sentinels);
  void printLoweredSentinels();
  void getAnalysisUsage(AnalysisUsage &AU) const {
    AU.addRequired<seahorn::SeaBuiltinsInfoWrapperPass>();
    AU.setPreservesAll();
  }
};

char EvalBranchSentinelPass::ID = 0;

bool EvalBranchSentinelPass::isBranchSentinelCall(const CallInst &ci) {
  using namespace seahorn;
  switch (m_SBI->getSeaBuiltinOp(ci)) {
  default:
    return false;
  case SeaBuiltinsOp::BRANCH_SENTINEL:
    return true;
  }
}

void EvalBranchSentinelPass::printLoweredSentinels() {
  for (auto keyF : m_condFalse) {
    if (m_condTrue.count(keyF) > 0 || m_unlowered.count(keyF) > 0) {
      continue;
    }
    INFO << "Conditional branch became false " << keyF;
  }
  for (auto keyT : m_condTrue) {
    if (m_condFalse.count(keyT) > 0 || m_unlowered.count(keyT) > 0) {
      continue;
    }
    INFO << "Conditional branch became true " << keyT;
  }
  for (auto e : m_unknown) {
    auto result = e.second ? "true" : "false";
    INFO << "(flaky) Conditional branch became " << result << ": "
         << *(e.first);
  }
}

void EvalBranchSentinelPass::processSentinels(
    SmallVector<CallInst *, 16> &sentinels) {
  // Due to jump threading a sentinal condition may split into 2 or more
  // with some instances being lowered and the others not.
  // To remove spurious results, we divide all sentinels into
  // 1) false 2) true and 3) unknown where unknown cannot be evaluated
  // statically.
  for (auto *sentinel : sentinels) {
    Value *cond = sentinel->getArgOperand(0);
    if (cond->getType()->isIntegerTy(1)) {
      if (llvm::ConstantInt *CI = dyn_cast<llvm::ConstantInt>(cond)) {
        bool isFalse = (CI->getValue() == 0);
        auto dloc = sentinel->getDebugLoc();
        SmallString<256> key;
        raw_svector_ostream out(key);
        if (dloc) {
          auto result = !isFalse ? "true" : "false";
          out << dloc->getFilename() << ":" << dloc->getLine() << ":"
              << dloc->getColumn();
          LOG("branch.sentinel",
              INFO << "Found branch sentinel(" << result << "):" << out.str());
        }
        if (isFalse) {
          if (dloc) {
            m_condFalse.insert(out.str());
          } else {
            m_unknown.insert({sentinel, false});
          }
        } else { // isTrue
          if (dloc) {
            m_condTrue.insert(out.str());
          } else {
            m_unknown.insert({sentinel, true});
          }
        }
      } else {
        auto dloc = sentinel->getDebugLoc();
        if (dloc) {
          SmallString<256> key;
          raw_svector_ostream out(key);
          out << dloc->getFilename() << ":" << dloc->getLine() << ":"
              << dloc->getColumn();
          m_unlowered.insert(out.str());
        } else {
          WARN << "Not handling unlowered sentinel without debugloc!";
        }
      }
    }
  }
}

bool EvalBranchSentinelPass::runOnFunction(Function &F) {
  SmallVector<CallInst *, 16> sentinels;

  for (auto &inst : instructions(F)) {
    if (auto *ci = dyn_cast<CallInst>(&inst)) {
      if (isBranchSentinelCall(*ci)) {
        sentinels.push_back(ci);
      }
    }
  }

  processSentinels(sentinels);
  printLoweredSentinels();

  return false;
}

Pass *createEvalBranchSentinelPassPass() {
  return new EvalBranchSentinelPass();
}

} // namespace seahorn

using namespace seahorn;
using namespace llvm;
INITIALIZE_PASS(EvalBranchSentinelPass, "eval-branch-sentinel-pass",
                "evaluates branch sentinel instructions", false, false)
