#ifndef HOUDINI__HH_
#define HOUDINI__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"

#include "ufo/Expr.hpp"

namespace seahorn
{
  using namespace llvm;

  class Houdini : public llvm::ModulePass
  {
  public:
    static char ID;
    
    std::map<Expr, int> bvar_map;

    Houdini() : ModulePass(ID) {}
    virtual ~Houdini() {}

    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "Houdini";}

    void printDB (const HornClauseDB &db);
    void printHello ();
    Expr guessCandidate(Expr pred);
    bool validateRule(Expr cand_app);
    bool validate_OldVersion(HornRule r, HornClauseDB &db);
    void workListAlgo(HornClauseDB &db);
  };
}

#endif /* HOUDNINI__HH_ */
