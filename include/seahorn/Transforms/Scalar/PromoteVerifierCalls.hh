#ifndef PROMOTEVERIFIERCALLS_H
#define PROMOTEVERIFIERCALLS_H
/**
 * Promote and normalize verifier specific calls such that __VERIFIER_assume()
 */

#include "llvm/IR/Function.h"
#include "llvm/IR/IRBuilder.h"
#include "llvm/IR/Module.h"
#include "llvm/Pass.h"

namespace seahorn {
using namespace llvm;

struct PromoteVerifierCalls : public ModulePass {
  static char ID;

  Function *m_assumeFn;
  Function *m_assertFn;
  Function *m_assertNotFn;
  Function *m_synthAssumeFn;
  Function *m_synthAssertFn;
  Function *m_errorFn;
  Function *m_failureFn; // to indicate failure. It can only appears in main.
  Function *m_is_deref;
  Function *m_assert_if;
  Function *m_is_modified;
  Function *m_reset_modified;
  Function *m_is_read;
  Function *m_reset_read;
  Function *m_is_alloc;
  Function *m_tracking_on;
  Function *m_tracking_off;
  Function *m_free;
  Function *m_set_shadowmem;
  Function *m_get_shadowmem;
  Function *m_mkOwn;
  Function *m_mkShr;
  Function *m_borMkBor;
  Function *m_borMkSuc;
  Function *m_begin_unique;
  Function *m_end_unique;
  Function *m_die;
  Function *m_move;
  Function *m_bor_mem2reg;
  Function *m_mov_reg2mem;
  Function *m_set_fatptr_slot;
  Function *m_get_fatptr_slot;

  PromoteVerifierCalls() : ModulePass(ID) {}

  bool runOnModule(Module &M) override;
  bool runOnFunction(Function &F);
  void getAnalysisUsage(AnalysisUsage &AU) const override;
  virtual StringRef getPassName() const override {
    return "PromoteVerifierCalls";
  }
};
} // namespace seahorn

#endif /* PROMOTEVERIFIERCALLS_H */
