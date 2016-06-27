#ifndef HOUDINI__HH_
#define HOUDINI__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
  using namespace llvm;

  class Houdini : public llvm::ModulePass
  {
  public:
    static char ID;

    Houdini() : ModulePass(ID) {}
    virtual ~Houdini() {}

    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "Houdini";}
  private:
    Expr guessCandidate(Expr pred);
    bool validateRule(Expr cand_app, HornifyModule &hm);
    void workListAlgo(HornClauseDB &db, HornifyModule &hm);

    template<typename OutputIterator>
    void get_all_bvars (Expr e, OutputIterator out);

    template<typename OutputIterator>
    void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out);
  };
}

#endif /* HOUDNINI__HH_ */
