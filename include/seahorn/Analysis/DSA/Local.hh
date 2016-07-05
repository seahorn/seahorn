#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/Pass.h"

#include "llvm/ADT/DenseSet.h"

#include "seahorn/Analysis/DSA/Graph.hh"

#include "boost/shared_ptr.hpp"

namespace llvm {
   class DataLayout;
   class TargetLibraryInfo;
}

using namespace llvm;

namespace seahorn
{
  namespace dsa
  {
    class Local : public ModulePass
    {
      typedef boost::shared_ptr<Graph> Graph_ptr;

      const DataLayout *m_dl;
      const TargetLibraryInfo *m_tli;
      DenseMap<const Function*, Graph_ptr> m_graphs;

    public:
      static char ID;
      Local ();
      
      void getAnalysisUsage (AnalysisUsage &AU) const override;

      bool runOnModule (Module &M) ;

      bool runOnFunction (Function &F);

      const char * getPassName() const {
        return "Dsa local pass";
      }
      
      const Graph& getGraph(const Function* F) const;
    };
  }
}
