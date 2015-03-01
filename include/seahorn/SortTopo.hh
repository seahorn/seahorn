#ifndef __SORT_TOPO_HH_
#define __SORT_TOPO_HH_

#include "llvm/IR/Function.h"
#include "llvm/ADT/PostOrderIterator.h"


namespace seahorn
{
  using namespace llvm;
  
  void RevTopoSort (const llvm::Function &F, 
                    std::vector<const BasicBlock*> &out);
}

                  

#endif
