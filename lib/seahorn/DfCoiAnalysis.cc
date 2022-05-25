#include "seahorn/DfCoiAnalysis.hh"

#include "seahorn/Support/SeaLog.hh"
#include "llvm/IR/BasicBlock.h"
#include "llvm/IR/CallSite.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include <cassert>

using namespace llvm;
namespace seahorn {

void DfCoiAnalysis::analyze(User &user) {
  constexpr auto shadowStoreSucc =
      hana::make_set("sea.reset_modified", "sea.free", "sea.set_shadowmem");

  constexpr auto shadowLoadSucc =
      hana::make_set("sea.is_modified", "sea.is_alloc", "sea.get_shadowmem");

  if (m_coi.count(&user))
    return;

  SmallVector<User *, 16> workList;

  workList.push_back(&user);
  while (!workList.empty()) {
    User &u = *workList.back();
    workList.pop_back();
    if (m_coi.count(&u))
      continue;
    m_coi.insert(&u);

    if (auto *LI = dyn_cast<LoadInst>(&u)) {
      auto *v = analyzeLoad(*LI);
      if (v) {
        workList.push_back(v);
      }
    } else if (auto *MI = dyn_cast<MemTransferInst>(&u)) {
      auto *v = analyzeMemTransfer(*MI);
      if (v) {
        workList.push_back(v);
      }
    } else if (auto *AI = dyn_cast<AllocaInst>(&u)) {
      auto *v = analyzeAllocaInst(*AI);
      if (v) {
        workList.push_back(v);
      }
    } else if (auto *CI = dyn_cast<CallInst>(&u)) {
      CallSite CS(CI);
      if (CS.getCalledFunction()) {
        if (CS.getCalledFunction()->getName().equals("shadow.mem.store")) {
          // insert store instruction that follows
          BasicBlock::iterator it(CI);
          ++it;
          assert(it != CI->getParent()->end());
          workList.push_back(&*it);
        } else if (hana::contains(shadowLoadSucc,
                                  CS.getCalledFunction()->getName())) {
          //  instruction that precedes has to be
          //  1. shadowmem.load
          BasicBlock::iterator it(CI);
          --it;
          if (auto *CI = dyn_cast<CallInst>(&*it)) {
            CallSite CS(CI);
            assert(CS.getCalledFunction()->getName().equals("shadow.mem.load"));
            workList.push_back(&*it);
          } else if (boost::hana::contains(shadowStoreSucc,
                                           CS.getCalledFunction()->getName())) {
            //  instruction that precedes has to be
            //  1. shadowmem.store
            BasicBlock::iterator it(CI);
            --it;
            if (auto *CI = dyn_cast<CallInst>(&*it)) {
              CallSite CS(CI);
              assert(
                  CS.getCalledFunction()->getName().equals("shadow.mem.store"));
              workList.push_back(&*it);
            }
          }
        }
      }
    }

    for (auto *val : u.operand_values()) {
      if (auto *user_op = dyn_cast<User>(val))
        workList.push_back(user_op);
      else
        m_coi.insert(val);
    }
  }
}

CallInst *DfCoiAnalysis::analyzeLoad(LoadInst &LI) {
  BasicBlock::iterator it(&LI);
  BasicBlock *parent = LI.getParent();
  assert(parent);
  if (it == parent->begin())
    return nullptr;

  --it;
  if (auto *CI = dyn_cast<CallInst>(&*it)) {
    CallSite CS(CI);
    assert(CS.getCalledFunction()->getName().equals("shadow.mem.load"));
    return CI;
  }
  return nullptr;
}

CallInst *DfCoiAnalysis::analyzeMemTransfer(MemTransferInst &MI) {
  BasicBlock::iterator it(&MI);
  BasicBlock *parent = MI.getParent();
  assert(parent);
  if (it == parent->begin())
    return nullptr;
  --it;
  if (it == parent->begin())
    return nullptr;
  --it;
  if (auto *CI = dyn_cast<CallInst>(&*it)) {
    CallSite CS(CI);
    assert(CS.getCalledFunction()->getName().equals("shadow.mem.trsfr.load"));
    return CI;
  }
  return nullptr;
}

CallInst *DfCoiAnalysis::analyzeAllocaInst(AllocaInst &AI) {
  BasicBlock::iterator it(&AI);
  BasicBlock *parent = AI.getParent();
  assert(parent);
  if (it == parent->begin())
    return nullptr;

  --it;
  if (auto *CI = dyn_cast<CallInst>(&*it)) {
    CallSite CS(CI);
    assert(CS.getCalledFunction()->getName().equals("shadow.mem.load") ||
           CS.getCalledFunction()->getName().equals("shadow.mem.store"));
    return CI;
  }
  return nullptr;
}
} // namespace seahorn
