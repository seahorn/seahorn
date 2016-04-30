#ifndef _HARNESS__HH_
#define _HARNESS__HH_

#include "llvm/IR/Module.h"

#include "seahorn/Bmc.hh"

#include <memory>

namespace seahorn
{
  using namespace llvm;

  std::unique_ptr<llvm::Module> createLLVMHarness (BmcTrace &trace);

}

#endif
