#ifndef __DSA_GLOBAL_HH_
#define __DSA_GLOBAL_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/ADT/DenseMap.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"

namespace llvm
{
  class DataLayout;
  class TargetLibraryInfo;
}

using namespace llvm;

namespace seahorn
{
  namespace dsa
  {

    class BottomUp : public ModulePass
    {
      const DataLayout *m_dl;
      const TargetLibraryInfo *m_tli;
      typedef std::shared_ptr<Graph> GraphRef;
      llvm::DenseMap<const Function *, GraphRef> m_graphs;
      Graph::SetFactory m_setFactory;
      
      void resolveCallSite (DsaCallSite &cs);

    public:

      static char ID;

      BottomUp ();

      void getAnalysisUsage (AnalysisUsage &AU) const override;

      bool runOnModule (Module &M) override;

      const char * getPassName() const override 
      { return "BottomUp DSA pass"; }

      Graph& getGraph (const Function &F) const;
      bool hasGraph (const Function &F) const;

    };
  }
}
#endif 
