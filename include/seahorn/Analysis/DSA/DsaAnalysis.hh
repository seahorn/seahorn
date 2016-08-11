#ifndef __DSA_ANALYSIS_HH_
#define __DSA_ANALYSIS_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/Global.hh"
#include "seahorn/Analysis/DSA/Info.hh"

/* Entry point for all Dsa clients */

namespace llvm 
{
    class DataLayout;
    class TargetLibraryInfo;
    class CallGraph;
    class Value;
}

namespace seahorn 
{
  namespace dsa 
  {

    class DsaAnalysis : public llvm::ModulePass
    {

      Graph::SetFactory m_setFactory;
      std::unique_ptr<GlobalAnalysis> m_ga;
      std::unique_ptr<InfoAnalysis> m_ia;

     public:
      
      static char ID;       
      
      DsaAnalysis (): ModulePass (ID), m_ga(nullptr), m_ia (nullptr) { }
      
      void getAnalysisUsage (llvm::AnalysisUsage &AU) const override;
      
      bool runOnModule (llvm::Module &M) override;
      
      const char * getPassName() const 
      { return "Dsa analysis: entry point for all Dsa clients"; }

      GlobalAnalysis& getDsaAnalysis () { return *m_ga; }

      bool hasDsaInfo ()const { return (bool) m_ia; }
      InfoAnalysis& getDsaInfo () 
      { 
        assert (hasDsaInfo ());
        return *m_ia; 
      }

    };

  }
}
#endif 
