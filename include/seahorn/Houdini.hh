#ifndef HOUDINI__HH_
#define HOUDINI__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

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
    static std::map<Expr,Expr> currentCandidates;

    Expr relToCand(Expr pred);
    void guessCandidate(HornClauseDB &db);
    bool validateRule(HornRule r, HornClauseDB &db, ZSolver<EZ3> &solver);
    void runHoudini(HornClauseDB &db, HornifyModule &hm, HornClauseDBWto &db_wto, int config);
    Expr fAppToCandApp(Expr fapp);
    Expr applyArgsToBvars(Expr cand, Expr fapp);
    ExprMap getBvarsToArgsMap(Expr fapp);
    void weakenRuleHeadCand(HornRule r, ZModel<EZ3> m);
    void addUsedRulesBackToWorkList(HornClauseDB &db, HornClauseDBWto &db_wto, std::list<HornRule> &workList, HornRule r);

    std::map<HornRule, ZSolver<EZ3>> assignEachRuleASolver(HornClauseDB &db, HornifyModule &hm);
    Expr extractTransitionRelation(HornRule r, HornClauseDB &db);
    bool validateRule_EachRuleASolver(HornRule r, HornClauseDB &db, ZSolver<EZ3> &solver);
    std::map<Expr, ZSolver<EZ3>> assignEachRelationASolver(HornClauseDB &db, HornifyModule &hm);
    bool validateRule_EachRelationASolver(HornRule r, HornClauseDB &db, ZSolver<EZ3> &solver);

    void run_naive(HornClauseDB &db, HornifyModule &hm, std::list<HornRule> &workList);
    void run_one_solver_per_rule(HornClauseDB &db, HornifyModule &hm, HornClauseDBWto &db_wto, std::list<HornRule> &workList);
    void run_one_solver_per_relation(HornClauseDB &db, HornifyModule &hm, HornClauseDBWto &db_wto, std::list<HornRule> &workList);

    void generatePositiveWitness(std::map<Expr, ExprVector> &relationToPositiveStateMap, HornClauseDB &db, HornifyModule &hm);
    void getReachableStates(std::map<Expr, ExprVector> &relationToPositiveStateMap, Expr from_pred, Expr from_pred_state, HornClauseDB &db, HornifyModule &hm);

    template<typename OutputIterator>
    void get_all_bvars (Expr e, OutputIterator out);

    template<typename OutputIterator>
    void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out);
  };
}

#endif /* HOUDNINI__HH_ */
