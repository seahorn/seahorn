#ifndef _LOCAL__H_
#define _LOCAL__H_

#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/Function.h"

namespace llvm {
class ReturnInst;
class TargetLibraryInfo;
} // namespace llvm
namespace seahorn {
class SeaBuiltinsInfo;
}
namespace seahorn {
/// mark all basic blocks that are ancestors of roots
void markAncestorBlocks(llvm::ArrayRef<const llvm::BasicBlock *> roots,
                        llvm::DenseSet<const llvm::BasicBlock *> &visited);

/// reduce the function to basic blocks in the region
void reduceToRegion(llvm::Function &F,
                    llvm::DenseSet<const llvm::BasicBlock *> &region,
                    SeaBuiltinsInfo &SBI);
/// reduce the function to the ancestors of blocks in exits
void reduceToAncestors(llvm::Function &F,
                       llvm::ArrayRef<const llvm::BasicBlock *> exits,
                       SeaBuiltinsInfo &SBI);
/// reduce the function to paths that lead to a return
void reduceToReturnPaths(llvm::Function &F, SeaBuiltinsInfo &SBI);

llvm::Function &createNewNondetFn(llvm::Module &m, llvm::Type &type,
                                  unsigned num, std::string prefix);

/// \brief Checks whether a basic block terminated with a return
/// A return instruction is returned in the last parameter
bool HasReturn(llvm::BasicBlock &bb, llvm::ReturnInst *&retInst);

/// \brief Checks whether a function has a return
/// A return instruction is returned in the last parameter
bool HasReturn(llvm::Function &f, llvm::ReturnInst *&retInst);

/// \brief Checks whether a function has a unique return
/// A return instruction is returned in the last parameter
bool HasUniqueReturn(llvm::Function &f, llvm::ReturnInst *&retInst);
} // namespace seahorn

namespace seahorn {
bool RecursivelyDeleteTriviallyDeadInstructions(
    llvm::Value *V, const llvm::TargetLibraryInfo *TLI = nullptr);
}

#endif /* _LOCAL__H_ */
