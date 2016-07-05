#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Module.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/Pass.h"

#include "llvm/IR/DataLayout.h"
#include "llvm/Target/TargetLibraryInfo.h"

#include "seahorn/Analysis/DSA/Graph.hh"
#include "seahorn/Analysis/DSA/Local.hh"
#include "seahorn/Analysis/DSA/Global.hh"

#include "avy/AvyDebug.h"

using namespace llvm;

namespace seahorn
{
  namespace dsa
  {

     Global::Global () 
         : ModulePass (ID), m_dl (nullptr), m_tli (nullptr), m_graph (nullptr) {}
  
     void Global::getAnalysisUsage (AnalysisUsage &AU) const
     {
       AU.addRequired<DataLayoutPass> ();
       AU.addRequired<TargetLibraryInfo> ();
       // TODO: add CallGraph
       // TODO: add dsa::Local
       AU.setPreservesAll ();
     }

     bool Global::runOnModule (Module &M)
     {
       m_dl = &getAnalysis<DataLayoutPass>().getDataLayout ();
       m_tli = &getAnalysis<TargetLibraryInfo> ();
       for (Function &F : M) runOnFunction (F);                
       return false;
     }

     bool Global::runOnFunction (Function &F)
     {
       if (F.isDeclaration () || F.empty ()) return false;
       // TODO
       return false;
     }

     char Global::ID = 0;

     Pass * createDsaGlobalPass () {return new Global ();}
      
  }
}
