#pragma once
#include "llvm/Pass.h"

namespace llvm {
class CallBase;
class Function;
class Module;
} // namespace llvm

namespace seahorn {

enum class SeaBuiltinsOp {
  ERROR,              /* verifier.error */
  FAIL,               /* seahorn.fail */
  ASSUME,             /* verifier.assume */
  ASSUME_NOT,         /* verifier.assume.not */
  ASSERT,             /* verifier.assert */
  ASSERT_NOT,         /* verifier.assert.not */
  SYNTH_ASSUME,       /* sea.synth.assume */
  SYNTH_ASSERT,       /* sea.synth.assert */
  IS_DEREFERENCEABLE, /* sea.is_dereferenceable */
  ASSERT_IF,          /* sea.assert.if */
  BRANCH_SENTINEL,    /* sea.branch_sentinel */
  IS_MODIFIED,        /* sea.is_modified */
  RESET_MODIFIED,     /* sea.reset_modified */
  IS_READ,            /* sea.is_read */
  RESET_READ,         /* sea.reset_read */
  IS_ALLOC,           /* sea.is_alloc */
  TRACKING_ON,        /* sea.tracking_on */
  TRACKING_OFF,       /* sea.tracking_off */
  FREE,               /* sea.free */
  UNKNOWN
};

class SeaBuiltinsInfo {
  void setCommonAttrs(llvm::Function &);
  llvm::Function *mkFailFn(llvm::Module &M);
  llvm::Function *mkErrorFn(llvm::Module &M);
  llvm::Function *mkAssertAssumeFn(llvm::Module &M, SeaBuiltinsOp);
  llvm::Function *mkIsDereferenceable(llvm::Module &M);
  llvm::Function *mkAssertIfFn(llvm::Module &M);
  llvm::Function *mkAssertFn(llvm::Module &M, SeaBuiltinsOp);
  llvm::Function *mkSynthAssume(llvm::Module &M);
  llvm::Function *mkSynthAssert(llvm::Module &M);
  llvm::Function *mkBranchSentinelFn(llvm::Module &M);
  llvm::Function *mkIsModifiedFn(llvm::Module &M);
  llvm::Function *mkResetModifiedFn(llvm::Module &M);
  llvm::Function *mkTrackingOnFn(llvm::Module &M);
  llvm::Function *mkTrackingOffFn(llvm::Module &M);
  llvm::Function *mkIsReadFn(llvm::Module &M);
  llvm::Function *mkResetReadFn(llvm::Module &M);
  llvm::Function *mkIsAllocFn(llvm::Module &M);
  llvm::Function *mkFreeFn(llvm::Module &M);

public:
  SeaBuiltinsOp getSeaBuiltinOp(const llvm::CallBase &cb) const;

  bool isSeaBuiltin(const llvm::CallBase &cb) const {
    return getSeaBuiltinOp(cb) != SeaBuiltinsOp::UNKNOWN;
  }

  llvm::Function *mkSeaBuiltinFn(SeaBuiltinsOp, llvm::Module &M);
};

class SeaBuiltinsInfoWrapperPass : public llvm::ImmutablePass {
  SeaBuiltinsInfo m_SBI;

public:
  static char ID;
  SeaBuiltinsInfoWrapperPass();

  SeaBuiltinsInfo &getSBI() { return m_SBI; }
};

} // namespace seahorn
