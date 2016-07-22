#ifndef __DSA_BOTTOM_UP_HH_
#define __DSA_BOTTOM_UP_HH_

#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"
#include "llvm/ADT/DenseMap.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/CallSite.hh"
#include "seahorn/Analysis/DSA/Mapper.hh"

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

    class BottomUpAnalysis {

     public:

      typedef std::shared_ptr<Graph> GraphRef;
      typedef llvm::DenseMap<const Function *, GraphRef> GraphMap;
      
     private:

      typedef std::shared_ptr<SimulationMapper> SimulationMapperRef;
      typedef boost::container::flat_map<const Instruction*, SimulationMapperRef> CalleeCallerMapping;

      const DataLayout &m_dl;
      const TargetLibraryInfo &m_tli;
      CallGraph &m_cg;
      CalleeCallerMapping m_callee_caller_map;

     public:

      static bool computeCalleeCallerMapping (const DsaCallSite &cs, 
                                              Graph &calleeG, Graph &callerG, 
                                              const bool onlyModified,
                                              SimulationMapper &simMap); 

      static void cloneAndResolveArguments (const DsaCallSite &CS, 
                                            Graph& calleeG, Graph& callerG);

      BottomUpAnalysis (const DataLayout &dl,
                        const TargetLibraryInfo &tli,
                        CallGraph &cg) 
          : m_dl(dl), m_tli(tli), m_cg(cg) {}

      bool runOnModule (Module &M, GraphMap &graphs);

      typedef typename CalleeCallerMapping::const_iterator callee_caller_mapping_const_iterator;
      
      callee_caller_mapping_const_iterator callee_caller_mapping_begin () const 
      { return m_callee_caller_map.begin(); }

      callee_caller_mapping_const_iterator callee_caller_mapping_end () const 
      { return m_callee_caller_map.end(); }
    };

    class BottomUp : public ModulePass
    {
      typedef typename BottomUpAnalysis::GraphRef GraphRef;
      typedef typename BottomUpAnalysis::GraphMap GraphMap;

      Graph::SetFactory m_setFactory;
      const DataLayout *m_dl;
      const TargetLibraryInfo *m_tli;
      GraphMap m_graphs;
      
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
