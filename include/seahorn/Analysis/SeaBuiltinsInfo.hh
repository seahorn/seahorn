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
  IS_DEREFERENCEABLE, /* sea.is_dereferenceable */
  UNKNOWN
};

class SeaBuiltinsInfo {
  void setCommonAttrs(llvm::Function &);
  llvm::Function *mkFailFn(llvm::Module &M);
  llvm::Function *mkErrorFn(llvm::Module &M);
  llvm::Function *mkAssertAssumeFn(llvm::Module &M, SeaBuiltinsOp);
  llvm::Function *mkIsDereferenceable(llvm::Module &M);

public:
  SeaBuiltinsOp getSeaBuiltinOp(const llvm::CallBase &cb) const;

  bool isSeaBuiltin(const llvm::CallBase &cb) const {
    return getSeaBuiltinOp(cb) != SeaBuiltinsOp::UNKNOWN;
  }

  llvm::Function *mkSeaBuiltinFn(SeaBuiltinsOp, llvm::Module &);
};

class SeaBuiltinsInfoWrapperPass : public llvm::ImmutablePass {
  SeaBuiltinsInfo m_SBI;

public:
  static char ID;
  SeaBuiltinsInfoWrapperPass();

  SeaBuiltinsInfo &getSBI() { return m_SBI; }
};

} // namespace seahorn
