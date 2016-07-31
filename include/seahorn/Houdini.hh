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

  class HoudiniPass : public llvm::ModulePass
  {
  public:
    static char ID;

    HoudiniPass() : ModulePass(ID) {}
    virtual ~HoudiniPass() {}

    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "Houdini";}
  };

  class GuessCandidates
  {
  public:
	  static std::map<Expr, Expr> guessCandidates(HornClauseDB &db);
	  //Simple templates
	  static Expr relToCand(Expr pred);
	  //Functions for generating complex invariants
	  static Expr applyComplexTemplates(Expr fdecl);
	  static void generateLemmasForOneBvar(Expr bvar, ExprVector &conjuncts);
  };

  class Houdini
  {
  public:
	  Houdini(HornifyModule &hm) : m_hm(hm)  {}
	  virtual ~Houdini() {}
  private:
	  HornifyModule &m_hm;
      std::map<Expr,Expr> currentCandidates;

    public:
      std::map<Expr,Expr>& getCurrentCandidates() {return currentCandidates;}
      void setInitialCandidatesSet(std::map<Expr, Expr> candidates) {currentCandidates = candidates;}

    public:
      void runHoudini(int config);

      //Utility Functions
      Expr fAppToCandApp(Expr fapp);
      Expr applyArgsToBvars(Expr cand, Expr fapp);
      ExprMap getBvarsToArgsMap(Expr fapp);

      Expr extractTransitionRelation(HornRule r, HornClauseDB &db);

      template<typename OutputIterator>
  	  void get_all_bvars (Expr e, OutputIterator out);

  	  template<typename OutputIterator>
  	  void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out);

      //Functions for generating Positive Examples
      void generatePositiveWitness(std::map<Expr, ExprVector> &relationToPositiveStateMap);
      void getReachableStates(std::map<Expr, ExprVector> &relationToPositiveStateMap, Expr from_pred, Expr from_pred_state);
      void getRuleHeadState(std::map<Expr, ExprVector> &relationToPositiveStateMap, HornRule r, Expr from_pred_state);

      //Add Houdini invs to default solver
      void addInvarCandsToProgramSolver();
  };

  class HoudiniContext
  {
  protected:
	  Houdini &m_houdini;
	  HornClauseDB &m_db;
	  HornifyModule &m_hm;
	  HornClauseDBWto &m_db_wto;
	  std::list<HornRule> &m_workList;
  public:
	  HoudiniContext(Houdini& houdini, HornClauseDB &db, HornifyModule &hm, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  m_houdini(houdini), m_db(db), m_hm(hm), m_db_wto(db_wto), m_workList(workList) {}
	  virtual void run() = 0;
	  virtual bool validateRule(HornRule r, ZSolver<EZ3> &solver) = 0;
	  void weakenRuleHeadCand(HornRule r, ZModel<EZ3> m);
	  void addUsedRulesBackToWorkList(HornClauseDB &db, HornClauseDBWto &db_wto, std::list<HornRule> &workList, HornRule r);
  };

  class Houdini_Naive : public HoudiniContext
  {
  private:
	  ZSolver<EZ3> m_solver;
  public:
	  Houdini_Naive(Houdini& houdini, HornClauseDB &db, HornifyModule &hm, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  HoudiniContext(houdini, db, hm, db_wto, workList), m_solver(hm.getZContext()) {}
	  void run();
	  bool validateRule(HornRule r, ZSolver<EZ3> &solver);
  };

  class Houdini_Each_Solver_Per_Rule : public HoudiniContext
  {
  private:
  	  std::map<HornRule, ZSolver<EZ3>> m_ruleToSolverMap;
  public:
  	  Houdini_Each_Solver_Per_Rule(Houdini& houdini, HornClauseDB &db, HornifyModule &hm, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
  		  HoudiniContext(houdini, db, hm, db_wto, workList), m_ruleToSolverMap(assignEachRuleASolver(db, hm)){}
  	  void run();
  	  bool validateRule(HornRule r, ZSolver<EZ3> &solver);
  	  std::map<HornRule, ZSolver<EZ3>> assignEachRuleASolver(HornClauseDB &db, HornifyModule &hm);
  };

  class Houdini_Each_Solver_Per_Relation : public HoudiniContext
  {
  private:
	  std::map<Expr, ZSolver<EZ3>> m_relationToSolverMap;
  public:
	  Houdini_Each_Solver_Per_Relation(Houdini& houdini, HornClauseDB &db, HornifyModule &hm, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  HoudiniContext(houdini, db, hm, db_wto, workList), m_relationToSolverMap(assignEachRelationASolver(db, hm)){}
	  void run();
	  bool validateRule(HornRule r, ZSolver<EZ3> &solver);
	  std::map<Expr, ZSolver<EZ3>> assignEachRelationASolver(HornClauseDB &db, HornifyModule &hm);
  };
}

#endif /* HOUDNINI__HH_ */
