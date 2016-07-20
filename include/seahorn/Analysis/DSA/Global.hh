#ifndef __DSA_GLOBAL_HH_
#define __DSA_GLOBAL_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"

namespace llvm
{
  class DataLayout;
  class TargetLibraryInfo;
  class CallGraph;
}

using namespace llvm;

namespace seahorn
{
  namespace dsa
  {

    class ContextInsensitiveGlobalAnalysis
    {
      const DataLayout &m_dl;
      const TargetLibraryInfo &m_tli;
      CallGraph &m_cg;
      
      void resolveArguments (DsaCallSite &cs, Graph& g);

    public:

      typedef typename Graph::SetFactory SetFactory;

      ContextInsensitiveGlobalAnalysis (const DataLayout &dl,
                                        const TargetLibraryInfo &tli,
                                        CallGraph &cg) 
          : m_dl(dl), m_tli(tli), m_cg(cg) {}

      bool runOnModule (Module &M, Graph& g, SetFactory &setFactory);

    };

    class ContextInsensitiveGlobal : public ModulePass
    {

      typedef std::unique_ptr<Graph> GraphRef;

      Graph::SetFactory m_setFactory;
      GraphRef m_graph;
      
    public:

      static char ID;

      ContextInsensitiveGlobal ();

      void getAnalysisUsage (AnalysisUsage &AU) const override;

      bool runOnModule (Module &M) override;

      const char * getPassName() const override 
      { return "Context-insensitive Dsa global pass"; }

      Graph& getGraph ();

      const Graph& getGraph () const;

    };
  }
}
#endif 
