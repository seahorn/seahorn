/**
SeaHorn Verification Framework
Copyright (c) 2016 Carnegie Mellon University.
All Rights Reserved.

THIS SOFTWARE IS PROVIDED "AS IS," WITH NO WARRANTIES
WHATSOEVER. CARNEGIE MELLON UNIVERSITY EXPRESSLY DISCLAIMS TO THE
FULLEST EXTENT PERMITTEDBY LAW ALL EXPRESS, IMPLIED, AND STATUTORY
WARRANTIES, INCLUDING, WITHOUT LIMITATION, THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE, AND
NON-INFRINGEMENT OF PROPRIETARY RIGHTS.

Released under a modified BSD license, please see license.txt for full
terms.

DM-0002198
*/

#include "llvm/Pass.h"
#include "llvm/Support/raw_ostream.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/Function.h"
#include "llvm/IR/Module.h"


#include "ufo/Smt/EZ3.hh"
#include "ufo/Stats.hh"

#include "seahorn/Bmc.hh"
#include "seahorn/UfoSymExec.hh"


namespace
{
  using namespace llvm;
  using namespace seahorn;
  using namespace ufo;
  
  class BmcPass : public llvm::ModulePass
  {
  public:
    static char ID;
    
    BmcPass () : llvm::ModulePass (ID) {}
    
    virtual bool runOnModule (Module &M)
    {
      for (Function &F : M)
        if (F.getName ().equals ("main")) return runOnFunction (F);
      return false;
    }
    
    void getAnalysisUsage (AnalysisUsage &AU) const
    {
      AU.setPreservesAll ();
      AU.addRequired<DataLayoutPass> ();
      AU.addRequired<CutPointGraph> ();
    }      

    virtual bool runOnFunction (Function &F)
    {
      
      const CutPointGraph &cpg = getAnalysis<CutPointGraph> (F);
      const CutPoint &src = cpg.getCp (F.getEntryBlock ());
      const CutPoint *dst = nullptr;
      
      for (auto &bb : F)
        if (llvm::isa<llvm::ReturnInst> (bb.getTerminator ()) && cpg.isCutPoint (bb))
        {
          dst = &cpg.getCp (bb);
          break;
        }

      if (dst == nullptr) return false;
      if (!cpg.getEdge (src, *dst)) return false;

      
      ExprFactory efac;
      UfoSmallSymExec sem (efac, *this, MEM);
      
      EZ3 zctx (efac);
      BmcEngine bmc (sem, zctx);
      
      bmc.addCutPoint (src);
      bmc.addCutPoint (*dst);
      
      bmc.encode ();
      auto res = bmc.solve ();
      
      if (res) outs () << "sat";
      else if (!res) outs () << "unsat";
      else outs () << "unknown";
      outs () << "\n";
      
      if (res) Stats::sset ("Result", "FALSE");
      else if (!res) Stats::sset ("Result", "TRUE");
      
      LOG ("cex", errs () << "Analyzed Function:\n" << F << "\n";);
      LOG ("cex", BmcTrace trace (bmc.getTrace ());
           trace.print (errs ()););
      
      return false;
    }
    
    virtual const char *getPassName () const {return "BmcPass";}
    
    
  };

  char BmcPass::ID = 0;
}
namespace seahorn
{
  Pass *createBmcPass () {return new BmcPass ();}
}

static llvm::RegisterPass<BmcPass>
X("bmc-pass", "Run BMC engine");


