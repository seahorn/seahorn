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
    static std::map<Expr, Expr> currentCandidates;

    Expr relToCand(Expr pred);
    void guessCandidate(HornClauseDB &db);
    bool validateRule(HornRule r, HornClauseDB &db, HornifyModule &hm);
    void runHoudini(HornClauseDB &db, HornifyModule &hm);
    Expr applyActualArgsToCand(Expr fapp);
    void weakenRuleHeadCand(HornRule r);
    HornClauseDB::RuleVector addUsedRulesBackToWorkList(HornClauseDB &db, HornClauseDB::RuleVector workList, Expr ruleHead_app);

    template<typename OutputIterator>
    void get_all_bvars (Expr e, OutputIterator out);

    template<typename OutputIterator>
    void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out);
  };
}

#endif /* HOUDNINI__HH_ */
