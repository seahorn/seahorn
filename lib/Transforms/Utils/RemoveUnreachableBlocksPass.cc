#include "seahorn/Transforms/Utils/RemoveUnreachableBlocksPass.hh"
#include "llvm/Transforms/Utils/Local.h"

#include "seahorn/config.h"

#include "sea_dsa/ShadowMem.hh"
#include "sea_dsa/DsaAnalysis.hh"

#ifdef HAVE_DSA
#include "dsa/DataStructure.h"
#include "dsa/AllocatorIdentification.h"
#include "dsa/AddressTakenAnalysis.h"
#include "dsa/Steensgaard.hh"
#endif

using namespace llvm;

namespace seahorn
{
  char RemoveUnreachableBlocksPass::ID = 0;

  bool RemoveUnreachableBlocksPass::runOnFunction (Function &F)
  {return removeUnreachableBlocks (F);}

  void RemoveUnreachableBlocksPass::getAnalysisUsage (AnalysisUsage &AU) const {
      #ifdef HAVE_DSA
      // Preserve DSA passes
      AU.addPreservedID(StdLibDataStructuresID);
      AU.addPreservedID(AddressTakenAnalysisID);
      AU.addPreservedID(AllocIdentifyID);
      AU.addPreservedID(LocalDataStructuresID);
      AU.addPreservedID(SteensgaardDataStructuresID);
      #endif
      // Preserve Sea-DSA passes
      AU.addPreservedID(sea_dsa::DsaAnalysis::ID);
      AU.addPreservedID(sea_dsa::ShadowMemPass::ID);      
  }
}

namespace seahorn {
    Pass* createRemoveUnreachableBlocksPass()
    {return new RemoveUnreachableBlocksPass();}
}
