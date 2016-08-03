#ifndef _LOCAL__H_
#define _LOCAL__H_

#include "llvm/ADT/DenseSet.h"
#include "llvm/IR/Function.h"


namespace seahorn
{
  using namespace llvm;
  /// mark all basic blocks that are ancestors of roots
  void markAncestorBlocks (ArrayRef<const BasicBlock*> roots, 
                           DenseSet<const BasicBlock*> &visited);
  
  /// reduce the function to basic blocks in the region
  void reduceToRegion (Function &F, DenseSet<const BasicBlock*> &region);
  /// reduce the function to the ancestors of blocks in exits
  void reduceToAncestors (Function &F, ArrayRef<const BasicBlock*> exits);
  /// reduce the function to paths that lead to a return
  void reduceToReturnPaths (Function &F);
  
  Function& createNewNondetFn (Module &m, Type &type, unsigned num, std::string prefix);
  


}

namespace llvm
{
  class TargetLibraryInfo;
}

namespace seahorn
{
  bool RecursivelyDeleteTriviallyDeadInstructions
  (llvm::Value *V,
   const llvm::TargetLibraryInfo *TLI = nullptr);
}


#endif /* _LOCAL__H_ */
