#ifndef _CEXHARNESS__HH_
#define _CEXHARNESS__HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/DataLayout.h"
#include "llvm/Analysis/TargetLibraryInfo.h"
#include "seahorn/Bmc.hh"


namespace seahorn
{
  using namespace llvm;

  std::unique_ptr<llvm::Module> createCexHarness (BmcTrace &trace, const DataLayout &dl,
        const TargetLibraryInfo &tli);

}

#endif
