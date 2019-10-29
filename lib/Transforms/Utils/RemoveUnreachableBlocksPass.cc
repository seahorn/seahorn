#include "seahorn/Transforms/Utils/RemoveUnreachableBlocksPass.hh"
#include "llvm/Transforms/Utils/Local.h"

#include "seahorn/config.h"

#include "seahorn/Transforms/Instrumentation/ShadowMemSeaDsa.hh"
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

      #ifdef USE_NEW_SHADOW_SEA_DSA
      AU.addPreservedID(sea_dsa::DsaAnalysis::ID);
      AU.addPreservedID(ShadowMemSeaDsa::ID);
      #endif
  }
}

namespace seahorn {
    Pass* createRemoveUnreachableBlocksPass()
    {return new RemoveUnreachableBlocksPass();}
}
