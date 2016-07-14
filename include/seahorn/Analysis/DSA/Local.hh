#ifndef __DSA_LOCAL_HH_
#define __DSA_LOCAL_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "llvm/ADT/DenseSet.h"

#include "seahorn/Analysis/DSA/Graph.hh"

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
    class LocalAnalysis
    {
      const DataLayout &m_dl;
      const TargetLibraryInfo &m_tli;

    public:
      LocalAnalysis (const DataLayout &dl,
                     const TargetLibraryInfo &tli) :
        m_dl(dl), m_tli(tli) {}

      void runOnFunction (Function &F, dsa::Graph &g);
      
    };
    class Local : public ModulePass
    {

      typedef std::shared_ptr<Graph> GraphRef;
      DenseMap<const Function*, GraphRef> m_graphs;
      
      const DataLayout *m_dl;
      const TargetLibraryInfo *m_tli;

    public:
      static char ID;

      Local ();
      
      void getAnalysisUsage (AnalysisUsage &AU) const override;

      bool runOnModule (Module &M) ;

      bool runOnFunction (Function &F);

      const char * getPassName() const 
      { return "Dsa local pass"; }
      
      bool hasGraph(const Function& F) const;

      const Graph& getGraph(const Function& F) const;
    };
  }
}
#endif 
