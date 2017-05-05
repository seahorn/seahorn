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
    enum GlobalAnalysisKind {
      CONTEXT_INSENSITIVE,
      CONTEXT_SENSITIVE
    };
    
    // Common API for global analyses
    class GlobalAnalysis 
    {
     protected:
      
      GlobalAnalysisKind _kind;
      
     public:
      
      GlobalAnalysis (GlobalAnalysisKind kind): _kind (kind) { }

      GlobalAnalysisKind kind () const { return _kind;}
      
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
          : GlobalAnalysis (CONTEXT_INSENSITIVE),
            m_dl (dl), m_tli (tli), m_cg (cg), m_setFactory (setFactory), 
            m_graph (nullptr) {}

      bool runOnModule (Module &M) override;

      const Graph& getGraph (const Function& fn) const override;

      Graph& getGraph (const Function& fn) override;
      
      bool hasGraph (const Function& fn) const override;
      
    };

    template <typename T>
    class WorkList 
    {
     public:
      WorkList ();
      bool empty () const;
      void enqueue (const T &e);
      const T& dequeue ();

     private:
      class impl;
      std::unique_ptr<impl> m_pimpl;
    };

    // Context-sensitive dsa analysis
    class ContextSensitiveGlobalAnalysis: public GlobalAnalysis 
    {
     public:
      
      typedef typename Graph::SetFactory SetFactory;

     private:

      typedef std::shared_ptr<Graph> GraphRef;
      typedef BottomUpAnalysis::GraphMap GraphMap;
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
          : GlobalAnalysis (CONTEXT_SENSITIVE), 
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

      virtual GlobalAnalysis& getGlobalAnalysis () = 0;

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

      GlobalAnalysis& getGlobalAnalysis ()  
      { return *(static_cast<GlobalAnalysis*> (&*m_ga)); } 

    };

  }
}


namespace seahorn
{
  namespace dsa
  {

    // Execute operation Op on each callsite until no more changes
    template<class GlobalAnalysis, class Op>
    class CallGraphClosure
    {

      GlobalAnalysis &m_ga;
      DsaCallGraph &m_dsaCG;
      WorkList<const Instruction*> m_w; 

      void exec_callsite (const DsaCallSite &cs, Graph& calleeG, Graph& callerG);

     public:

      CallGraphClosure (GlobalAnalysis &ga, DsaCallGraph &dsaCG)
          : m_ga (ga), m_dsaCG (dsaCG)  {}
      
      bool runOnModule (Module &M);

    };

    // Propagate unique scalar flag across callsites
    class UniqueScalar 
    {
      DsaCallGraph &m_dsaCG;
      WorkList<const Instruction*> &m_w;

     public:
      
      UniqueScalar (DsaCallGraph &dsaCG, WorkList<const Instruction*> &w)
          : m_dsaCG (dsaCG), m_w (w) {}

      void runOnCallSite (const DsaCallSite &cs, Node &calleeN, Node &callerN);
    };

    // Propagate allocation sites across callsites
    class AllocaSite
    {
      DsaCallGraph &m_dsaCG;
      WorkList<const Instruction*> &m_w;

     public:
      
      AllocaSite (DsaCallGraph &dsaCG, WorkList<const Instruction*> &w)
          : m_dsaCG (dsaCG), m_w (w) {}

      void runOnCallSite (const DsaCallSite &cs, Node &calleeN, Node &callerN);
    };


  } // end namespace
} // end namespace
#endif 
