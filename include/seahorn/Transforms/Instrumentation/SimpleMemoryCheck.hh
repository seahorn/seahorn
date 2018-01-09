#ifndef SIMPLE_MEMORY_CHECK__HH
#define SIMPLE_MEMORY_CHECK__HH

namespace llvm {
class ModulePass;
}

namespace seahorn {
llvm::ModulePass *CreateSimpleMemoryCheckPass();
}

#endif
