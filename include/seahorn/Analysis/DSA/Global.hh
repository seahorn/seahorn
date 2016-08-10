#ifndef __DSA_GLOBAL_HH_
#define __DSA_GLOBAL_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/BottomUp.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"
#include "seahorn/Analysis/DSA/CallGraph.hh"

#include "boost/container/flat_set.hpp"

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

    // Common API for global analyses
    class GlobalAnalysis 
    {
     public:
      
      GlobalAnalysis () { }

      virtual bool runOnModule (Module &M) = 0;

      virtual const Graph& getGraph (const Function &F) const = 0;

      virtual Graph& getGraph (const Function &F) = 0;

      virtual bool hasGraph (const Function &F) const = 0 ;
    };  

    // Context-insensitive dsa analysis
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
      // functions represented in m_graph
      boost::container::flat_set<const Function*> m_fns;

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

    // Context-sensitive dsa analysis
    class ContextSensitiveGlobalAnalysis: public GlobalAnalysis 
    {
     public:
      
      typedef typename Graph::SetFactory SetFactory;

     private:

      typedef std::shared_ptr<Graph> GraphRef;
      typedef BottomUpAnalysis::GraphMap GraphMap;
      typedef std::vector<const Instruction*> Worklist;
      enum PropagationKind {DOWN, UP, NONE};

      const DataLayout &m_dl;
      const TargetLibraryInfo &m_tli;
      CallGraph &m_cg;
      SetFactory &m_setFactory;
     public:
      GraphMap m_graphs;

      void cloneAndResolveArguments (const DsaCallSite &cs, 
                                     Graph& callerG, Graph& calleeG);
      
      PropagationKind decidePropagation (const DsaCallSite& cs, 
                                         Graph &callerG, Graph& calleeG);
      
      void propagateTopDown(const DsaCallSite& cs, Graph &callerG, Graph& calleeG); 

      void propagateBottomUp(const DsaCallSite& cs, Graph &calleeG, Graph& callerG); 
            
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

    class DsaGlobalPass: public ModulePass 
    {
     protected:
      
      DsaGlobalPass (char &ID): ModulePass (ID) { }

     public:

      virtual const Graph& getGraph (const Function &F) const = 0;

      virtual Graph& getGraph (const Function &F) = 0;

      virtual bool hasGraph (const Function &F) const = 0 ;
    };  

    class ContextInsensitiveGlobal : public DsaGlobalPass
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

      Graph& getGraph (const Function &fn) override;

      bool hasGraph (const Function &fn) const override;

      GlobalAnalysis& getGlobalAnalysis ()  
      { return *(static_cast<GlobalAnalysis*> (&*m_ga)); } 

    };

    class ContextSensitiveGlobal : public DsaGlobalPass
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

      GlobalAnalysis& getGlobalAnalysis ()  
      { return *(static_cast<GlobalAnalysis*> (&*m_ga)); } 

    };

  }
}


namespace seahorn
{
  namespace dsa
  {

    // XXX: for now, it makes sense to instantiate the template
    // parameter only with ContextSensitiveGlobalAnalysis but in the
    // future we might have other context-sensitive analyses.
    template<class GlobalAnalysis>
    class UniqueScalarAnalysis 
    {

      GlobalAnalysis &m_ga;
      DsaCallGraph &m_dsaCG;

      void join (const DsaCallSite &cs, Node& calleeN, Node& callerN,
                 std::vector<const Instruction*> &w);
      
      void normalize (const DsaCallSite &cs, Graph& calleeG, Graph& callerG,
                      std::vector<const Instruction*> &w);

     public:

      UniqueScalarAnalysis (GlobalAnalysis &ga, DsaCallGraph &dsaCG)
          : m_ga (ga), m_dsaCG (dsaCG)  {}
      
      bool runOnModule (Module &M);

    };
  }
}
#endif 
