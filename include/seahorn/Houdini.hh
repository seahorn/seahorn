#ifndef HOUDINI__HH_
#define HOUDINI__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/GuessCandidates.hh"
#include "seahorn/HornDbModel.hh"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include "seahorn/HornClauseDBWto.hh"

#include <list>

namespace seahorn
{
  using namespace llvm;

  class HoudiniPass : public llvm::ModulePass
  {
  public:
    static char ID;

    HoudiniPass() : ModulePass(ID) {}
    virtual ~HoudiniPass() {}

    virtual bool runOnModule (Module &M) override;
    virtual void getAnalysisUsage (AnalysisUsage &AU) const override;
    virtual StringRef getPassName () const override {return "Houdini";}
  };

  class Houdini
  {
  public:
	  Houdini(HornifyModule &hm) : m_hm(hm)  {}
	  virtual ~Houdini() {}
  private:
	  HornifyModule &m_hm;
	  HornDbModel m_candidate_model;


    public:
      HornifyModule& getHornifyModule() {return m_hm;}
      HornDbModel& getCandidateModel() {return m_candidate_model;}

    public:
      void runHoudini(int config);

      void guessCandidates(HornClauseDB &db);

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
	  HornClauseDBWto &m_db_wto;
	  std::list<HornRule> &m_workList;
  public:
	  HoudiniContext(Houdini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  m_houdini(houdini), m_db_wto(db_wto), m_workList(workList) {}
    virtual ~HoudiniContext() = default;
	  virtual void run() = 0;
	  virtual bool validateRule(HornRule r, ZSolver<EZ3> &solver) = 0;
	  void weakenRuleHeadCand(HornRule r, ZModel<EZ3> m);
	  void addUsedRulesBackToWorkList(HornClauseDBWto &db_wto, std::list<HornRule> &workList, HornRule r);
  };

  class Houdini_Naive : public HoudiniContext
  {
  private:
	  ZSolver<EZ3> m_solver;
  public:
	  Houdini_Naive(Houdini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  HoudiniContext(houdini, db_wto, workList), m_solver(houdini.getHornifyModule().getZContext()) {}
	  void run() override;
	  bool validateRule(HornRule r, ZSolver<EZ3> &solver) override;
  };

  class Houdini_Each_Solver_Per_Rule : public HoudiniContext
  {
  private:
  	  std::map<HornRule, ZSolver<EZ3>> m_ruleToSolverMap;
  public:
  	  Houdini_Each_Solver_Per_Rule(Houdini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
  		  HoudiniContext(houdini, db_wto, workList), m_ruleToSolverMap(assignEachRuleASolver()){}
  	  void run() override;
  	  bool validateRule(HornRule r, ZSolver<EZ3> &solver) override;
  	  std::map<HornRule, ZSolver<EZ3>> assignEachRuleASolver();
  };

class Houdini_Each_Solver_Per_Relation : public HoudiniContext {
  private:
	  std::map<Expr, ZSolver<EZ3>> m_relationToSolverMap;
  public:
	  Houdini_Each_Solver_Per_Relation(Houdini& houdini, HornClauseDBWto &db_wto, std::list<HornRule> &workList) :
		  HoudiniContext(houdini, db_wto, workList), m_relationToSolverMap(assignEachRelationASolver()){}
	  void run() override;
	  bool validateRule(HornRule r, ZSolver<EZ3> &solver) override;
	  std::map<Expr, ZSolver<EZ3>> assignEachRelationASolver();
  };
}

#endif /* HOUDNINI__HH_ */
