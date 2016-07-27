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

    class GlobalAnalysis {
     public:
      
      GlobalAnalysis () { }

      virtual bool runOnModule (Module &M) = 0;

      virtual const Graph& getGraph (const Function &F) const = 0;

      virtual Graph& getGraph (const Function &F) = 0;

      virtual bool hasGraph (const Function &F) const = 0 ;
    };  


    class ContextInsensitiveGlobalAnalysis: public GlobalAnalysis
    {

     public:
      
      typedef typename Graph::SetFactory SetFactory;

     private:

      typedef std::unique_ptr<Graph> GraphRef;

      const DataLayout &m_dl;
      const TargetLibraryInfo &m_tli;
      CallGraph &m_cg;
      SetFactory &m_setFactory;
      GraphRef m_graph;

      void resolveArguments (DsaCallSite &cs, Graph& g);

     public:
      
      ContextInsensitiveGlobalAnalysis (const DataLayout &dl, 
                                        const TargetLibraryInfo &tli,
                                        CallGraph &cg, SetFactory &setFactory) 
          : GlobalAnalysis (),
            m_dl (dl), m_tli (tli), m_cg (cg), m_setFactory (setFactory), 
            m_graph (nullptr) {}

      bool runOnModule (Module &M) override;

      const Graph& getGraph (const Function& fn) const override;

      Graph& getGraph (const Function& fn) override;
      
      bool hasGraph (const Function& fn) const override;
      
    };
  
    class ContextSensitiveGlobalAnalysis: public GlobalAnalysis {

     public:
      
      typedef typename Graph::SetFactory SetFactory;

     private:

      typedef std::shared_ptr<Graph> GraphRef;
      typedef llvm::DenseMap<const Function *, GraphRef> GraphMap;

      const DataLayout &m_dl;
      const TargetLibraryInfo &m_tli;
      CallGraph &m_cg;
      SetFactory &m_setFactory;
      GraphMap m_graphs;

      typedef std::vector<const Instruction*> Worklist;

      enum PropagationKind {DOWN, UP, NONE};
      
      PropagationKind decidePropagation 
      (const DsaCallSite& cs, Graph &callerG, Graph& calleeG);
      
      void propagateTopDown 
      (const DsaCallSite& cs, Graph &callerG, Graph& calleeG, Worklist &w);

      void propagateBottomUp 
      (const DsaCallSite& cs, Graph &calleeG, Graph& callerG, Worklist &w);
      
      // Sanity check
      bool checkNoMorePropagation ();

     public:

      ContextSensitiveGlobalAnalysis (const DataLayout &dl,
                                      const TargetLibraryInfo &tli,
                                      CallGraph &cg, SetFactory &setFactory) 
          : GlobalAnalysis (), 
            m_dl(dl), m_tli(tli), m_cg(cg), m_setFactory (setFactory) {}
      
      bool runOnModule (Module &M) override;

      const Graph& getGraph (const Function& fn) const override;

      Graph& getGraph (const Function& fn) override;
      
      bool hasGraph (const Function& fn) const override;
    };

    // Llvm passes

    class DsaGlobalPass {
     public:
      
      DsaGlobalPass () { }

      virtual const Graph& getGraph (const Function &F) const = 0;

      virtual Graph& getGraph (const Function &F) = 0;

      virtual bool hasGraph (const Function &F) const = 0 ;
    };  

    class ContextInsensitiveGlobal : public ModulePass, DsaGlobalPass
    {
      
      Graph::SetFactory m_setFactory;
      std::unique_ptr<ContextInsensitiveGlobalAnalysis> m_ga;

     public:
      
      static char ID;
      
      ContextInsensitiveGlobal ();
      
      void getAnalysisUsage (AnalysisUsage &AU) const override;
      
      bool runOnModule (Module &M) override;
      
      const char * getPassName() const override 
      { return "Context-insensitive Dsa global pass"; }

      const Graph& getGraph (const Function &fn) const override;

      Graph& getGraph (const Function &fn) override ;

      bool hasGraph (const Function &fn) const override;

    };

    class ContextSensitiveGlobal : public ModulePass, DsaGlobalPass
    {
      Graph::SetFactory m_setFactory;
      std::unique_ptr<ContextSensitiveGlobalAnalysis> m_ga;      
      
    public:

      static char ID;

      ContextSensitiveGlobal ();

      void getAnalysisUsage (AnalysisUsage &AU) const override;

      bool runOnModule (Module &M) override;

      const char * getPassName() const override 
      { return "Context sensitive global DSA pass"; }

      const Graph& getGraph (const Function &fn) const override;

      Graph& getGraph (const Function &fn) override;

      bool hasGraph (const Function &fn) const override;
    };

  }
}
#endif 
