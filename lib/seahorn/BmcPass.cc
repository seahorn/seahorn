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
#include "ufo/Passes/NameValues.hpp"

#include "seahorn/Bmc.hh"
#include "seahorn/UfoSymExec.hh"
#include "seahorn/BvSymExec.hh"

#include "seahorn/Analysis/CanFail.hh"

namespace
{
  using namespace llvm;
  using namespace seahorn;
  using namespace ufo;
  
  class BmcPass : public llvm::ModulePass
  {
    /// output stream for encoded bmc problem
    raw_ostream *m_out;
    /// true if to run the solver, false if encode only
    bool m_solve;
  public:
    static char ID;
    
    BmcPass (raw_ostream *out = nullptr, bool solve = true) :
      llvm::ModulePass (ID), m_out(out), m_solve (solve) {}
    
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
      
      AU.addRequired<seahorn::CanFail> ();
      AU.addRequired<ufo::NameValues>();
      AU.addRequired<seahorn::TopologicalOrder>();
      AU.addRequired<CutPointGraph> ();
    }      

    virtual bool runOnFunction (Function &F)
    {
      
      const CutPointGraph &cpg = getAnalysis<CutPointGraph> (F);
      const CutPoint &src = cpg.getCp (F.getEntryBlock ());
      const CutPoint *dst = nullptr;
      
      // -- find return instruction. Assume it is unique
      for (auto &bb : F)
        if (llvm::isa<llvm::ReturnInst> (bb.getTerminator ()) && cpg.isCutPoint (bb))
        {
          dst = &cpg.getCp (bb);
          break;
        }

      if (dst == nullptr) return false;
      if (!cpg.getEdge (src, *dst)) return false;

      
      ExprFactory efac;
      BvSmallSymExec sem (efac, *this, MEM);
      
      EZ3 zctx (efac);
      BmcEngine bmc (sem, zctx);
      
      bmc.addCutPoint (src);
      bmc.addCutPoint (*dst);
      LOG("bmc", errs () << "BMC from: " << src.bb ().getName ()
          << " to " << dst->bb ().getName () << "\n";);
      
      bmc.encode ();
      if (m_out) bmc.toSmtLib (*m_out);
      
      if (!m_solve)
        {
          LOG ("bmc", errs () << "Stopping before solving\n";);
          return false;
        }
      
      Stats::resume ("BMC");
      auto res = bmc.solve ();
      Stats::stop ("BMC");
     
      if (res) outs () << "sat";
      else if (!res) outs () << "unsat";
      else outs () << "unknown";
      outs () << "\n";
      
      if (res) Stats::sset ("Result", "FALSE");
      else if (!res) Stats::sset ("Result", "TRUE");
      
      LOG ("bmc",
           ExprVector core;
           if (!res) bmc.unsatCore (core);
           errs () << "CORE BEGIN\n";
           for (auto c : core) errs () << *c << "\n";
           errs () << "CORE END\n";
           );
      
      LOG ("cex", 
           if (res) 
             {
               errs () << "Analyzed Function:\n" << F << "\n";
               BmcTrace trace (bmc.getTrace ());
               trace.print (errs ());
             });
      
      return false;
    }
    
    virtual const char *getPassName () const {return "BmcPass";}
    
    
  };

  char BmcPass::ID = 0;
}
namespace seahorn
{
  Pass *createBmcPass (raw_ostream *out, bool solve)
  {return new BmcPass (out, solve);}
}

static llvm::RegisterPass<BmcPass>
X("bmc-pass", "Run BMC engine");


