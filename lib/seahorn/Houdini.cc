#include "seahorn/Houdini.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/GuessCandidates.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include <vector>
#include <boost/logic/tribool.hpp>
#include "seahorn/HornClauseDBWto.hh"
#include <algorithm>

#include "seahorn/Support/Stats.hh"

using namespace llvm;

namespace seahorn
{
  #define SAT_OR_INDETERMIN true
  #define UNSAT false

  #define NAIVE 0
  #define EACH_RULE_A_SOLVER 1
  #define EACH_RELATION_A_SOLVER 2

  /*HoudiniPass methods begin*/

  char HoudiniPass::ID = 0;

  bool HoudiniPass::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    //Use commandline option to replace it.
    int config = EACH_RULE_A_SOLVER;

    Stats::resume ("Houdini inv");
    Houdini houdini(hm);
    houdini.guessCandidates(hm.getHornClauseDB());
    houdini.runHoudini(config);
    Stats::stop ("Houdini inv");

    return false;
  }

  void HoudiniPass::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  /*HoudiniPass methods end*/

  /*Houdini methods begin*/

  void Houdini::addInvarCandsToProgramSolver()
  {
	  auto &db = m_hm.getHornClauseDB();
	  for(Expr rel : db.getRelations())
	  {
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr arg_i = bind::fapp(bind::bvar(i, arg_i_type));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);
		  Expr cand_app = m_candidate_model.getDef(fapp);
		  LOG("candidates", errs() << "HEAD: " << *fapp << "\n";);
		  LOG("candidates", errs() << "CAND: " << *cand_app << "\n";);
		  if(!isOpX<TRUE>(cand_app))
		  {
			  LOG("candidates", errs() << "ADD CONSTRAINT\n";);
			  db.addConstraint(fapp, cand_app);
		  }
	  }
//	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
//	  {
//			HornRule r = *it;
//			Expr rhead_app = r.head();
//			Expr rhead_cand_app = m_candidate_model.getDef(rhead_app);
//			LOG("candidates", errs() << "HEAD: " << *rhead_app << "\n";);
//			LOG("candidates", errs() << "CAND: " << *rhead_cand_app << "\n";);
//			if(!isOpX<TRUE>(rhead_cand_app))
//			{
//				LOG("candidates", errs() << "ADD CONSTRAINT\n";);
//				db.addConstraint(rhead_app, rhead_cand_app);
//			}
//	  }
  }

  void Houdini::guessCandidates(HornClauseDB &db)
  {
	  for(Expr rel : db.getRelations())
	  {
		  ExprMap bvarToArgMap;
		  ExprVector arg_list;
		  for(int i=0; i<bind::domainSz(rel); i++)
		  {
			  Expr arg_i_type = bind::domainTy(rel, i);
			  Expr bvar_i = bind::bvar(i, arg_i_type);
			  Expr arg_i = bind::fapp(bvar_i);
			  bvarToArgMap.insert(std::make_pair(bvar_i, arg_i));
			  arg_list.push_back(arg_i);
		  }
		  Expr fapp = bind::fapp(rel, arg_list);

		  ExprVector lemmas = relToCand(rel);
		  Expr cand;
		  if(lemmas.size() == 1)
		  {
			  cand = lemmas[0];
		  }
		  else
		  {
			  cand = mknary<AND>(lemmas.begin(), lemmas.end());
		  }
		  Expr cand_app = replace(cand, bvarToArgMap);

		  m_candidate_model.addDef(fapp, cand_app);
	  }
  }

  /*
   * Main loop of Houdini algorithm
   */
  void Houdini::runHoudini(int config)
  {
	  //load the Horn clause database
	  auto &db = m_hm.getHornClauseDB ();
	  db.buildIndexes ();

	  //build the wto
	  HornClauseDBCallGraph callgraph(db);
	  HornClauseDBWto db_wto(callgraph);
	  db_wto.buildWto();

	  //generate positive states
	  std::map<Expr, ExprVector> relationToPositiveStateMap;
	  //generatePositiveWitness(relationToPositiveStateMap, db, hm);

//	  LOG("houdini", errs() << "CAND MAP:\n";);
//	  LOG("houdini", errs() << "MAP SIZE: " << m_candidate_model.m_defs.size() << "\n";);
//	  for(std::map<Expr, Expr>::iterator it = m_candidate_model.m_defs.begin(); it!= m_candidate_model.m_defs.end(); ++it)
//	  {
//		LOG("houdini", errs() << "PRED: " << *(it->first) << "\n";);
//		LOG("houdini", errs() << "CAND: " << *(it->second) << "\n";);
//	  }

	  std::list<HornRule> workList;
	  workList.insert(workList.end(), db.getRules().begin(), db.getRules().end());
	  workList.reverse();

	  if (config == EACH_RULE_A_SOLVER)
	  {
		  Houdini_Each_Solver_Per_Rule houdini_solver_per_rule(*this, db_wto, workList);
		  houdini_solver_per_rule.run();
	  }
	  else if (config == EACH_RELATION_A_SOLVER)
	  {
		  Houdini_Each_Solver_Per_Relation houdini_solver_per_relation(*this, db_wto, workList);
		  houdini_solver_per_relation.run();
	  }
	  else if (config == NAIVE)
	  {
		  Houdini_Naive houdini_naive(*this, db_wto, workList);
		  houdini_naive.run();
	  }

	  addInvarCandsToProgramSolver();
  }

  void Houdini_Naive::run()
  {
  	  while(!m_workList.empty())
  	  {
  		  LOG("houdini", errs() << "WORKLIST SIZE: " << m_workList.size() << "\n";);
  		  HornRule r = m_workList.front();
  		  m_workList.pop_front();
  		  LOG("houdini", errs() << "RULE HEAD: " << *(r.head()) << "\n";);
  		  LOG("houdini", errs() << "RULE BODY: " << *(r.body()) << "\n";);
  		  while (validateRule(r, m_solver) != UNSAT)
  		  {
  			  addUsedRulesBackToWorkList(m_db_wto, m_workList, r);
  			  ZModel<EZ3> m = m_solver.getModel();
  			  weakenRuleHeadCand(r, m);
  		  }
  	  }
  }

  bool Houdini_Naive::validateRule(HornRule r, ZSolver<EZ3> &solver)
  {
	  solver.reset();

	  auto &m_hm = m_houdini.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();

	  Expr ruleHead_cand_app = m_houdini.getCandidateModel().getDef(r.head());
	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);
	  solver.assertExpr(neg_ruleHead_cand_app);

	  Expr ruleBody = r.body();
	  ExprVector body_pred_apps;
	  get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));
	  for(Expr body_app : body_pred_apps)
	  {
		  solver.assertExpr(m_houdini.getCandidateModel().getDef(body_app)); //add each body predicate app
	  }

	  solver.assertExpr(extractTransitionRelation(r, db));

	  //solver.toSmtLib(errs());
	  boost::tribool isSat = solver.solve();
	  if(isSat)
	  {
		  LOG("houdini", errs() << "SAT\n";);
		  return SAT_OR_INDETERMIN;
	  }
	  else if(!isSat)
	  {
		  LOG("houdini", errs() << "UNSAT\n";);
		  return UNSAT;
	  }
	  else //if indeterminate
	  {
		  LOG("houdini", errs() << "INDETERMINATE\n";);
		  return SAT_OR_INDETERMIN;
	  }
  }

  void Houdini_Each_Solver_Per_Rule::run()
  {
	  while(!m_workList.empty())
	  {
		  LOG("houdini", errs() << "WORKLIST SIZE: " << m_workList.size() << "\n";);
		  HornRule r = m_workList.front();
		  m_workList.pop_front();
		  LOG("houdini", errs() << "RULE HEAD: " << *(r.head()) << "\n";);
		  LOG("houdini", errs() << "RULE BODY: " << *(r.body()) << "\n";);

		  assert(m_ruleToSolverMap.find(r) != m_ruleToSolverMap.end());

		  ZSolver<EZ3> &solver = m_ruleToSolverMap.find(r)->second;

		  while (validateRule(r, solver) != UNSAT)
		  {
			  addUsedRulesBackToWorkList(m_db_wto, m_workList, r);
			  ZModel<EZ3> m = solver.getModel();
			  weakenRuleHeadCand(r, m);
			  solver.pop();
			  solver.push();
			  //LOG("houdini", errs() << "AFTER POP: \n";);
			  //solver.toSmtLib(outs());
		  }
		  solver.pop();
		  solver.push();
	  }
  }

  bool Houdini_Each_Solver_Per_Rule::validateRule(HornRule r, ZSolver<EZ3> &solver)
  {
  	  /////////////////////////////////////////
  	  /*LOG("houdini", errs() << "CAND MAPS:\n";);
  	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it!= db.getRules().end(); ++it)
  	  {
  		  HornRule r = *it;
  		  Expr rhead_app = r.head();
  		  Expr rhead_cand_app = fAppToCandApp(rhead_app);
  		  LOG("houdini", errs() << "HEAD: " << *rhead_app << "\n";);
  		  LOG("houdini", errs() << "CAND: " << *rhead_cand_app << "\n";);
  	  }*/
  	  ////////////////////////////////////////
	  auto &m_hm = m_houdini.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();

	  Expr ruleHead_cand_app = m_houdini.getCandidateModel().getDef(r.head());
  	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);
  	  solver.assertExpr(neg_ruleHead_cand_app);

  	  Expr ruleBody = r.body();
  	  ExprVector body_pred_apps;
  	  get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));
  	  for(Expr body_app : body_pred_apps)
	  {
		  solver.assertExpr(m_houdini.getCandidateModel().getDef(body_app)); //add each body predicate app
	  }

  	  //LOG("houdini", errs() << "AFTER PUSH: \n";);
  	  //solver.toSmtLib(errs());
  	  boost::tribool isSat = solver.solve();
  	  if(isSat)
  	  {
  		  LOG("houdini", errs() << "SAT\n";);
  	  	  return SAT_OR_INDETERMIN;
  	  }
  	  else if(!isSat)
  	  {
  		  LOG("houdini", errs() << "UNSAT\n";);
  	  	  return UNSAT;
  	  }
  	  else //if indeterminate
  	  {
  		  LOG("houdini", errs() << "INDETERMINATE\n";);
  		  return SAT_OR_INDETERMIN;
  	  }
  }

  std::map<HornRule, ZSolver<EZ3>> Houdini_Each_Solver_Per_Rule::assignEachRuleASolver()
  {
	  auto &m_hm = m_houdini.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();
  	  std::map<HornRule, ZSolver<EZ3>> ruleToSolverMap;
  	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
  	  {
  		  HornRule r = *it;
  		  Expr tr = extractTransitionRelation(r, db);
  		  ZSolver<EZ3> solver(m_hm.getZContext());
  		  solver.assertExpr(tr);
  		  solver.push();

  		  ruleToSolverMap.insert(std::make_pair(r, solver));
  	  }
  	  return ruleToSolverMap;
  }

  void Houdini_Each_Solver_Per_Relation::run()
  {
	  while(!m_workList.empty())
	  {
		  LOG("houdini", errs() << "WORKLIST SIZE: " << m_workList.size() << "\n";);
		  HornRule r = m_workList.front();
		  m_workList.pop_front();
		  LOG("houdini", errs() << "RULE HEAD: " << *(r.head()) << "\n";);
		  LOG("houdini", errs() << "RULE BODY: " << *(r.body()) << "\n";);

		  assert(m_relationToSolverMap.find(r.head()) != m_relationToSolverMap.end());

		  ZSolver<EZ3> &solver = m_relationToSolverMap.find(r.head())->second;

		  while (validateRule(r, solver) != UNSAT)
		  {
			  addUsedRulesBackToWorkList(m_db_wto, m_workList, r);
			  ZModel<EZ3> m = solver.getModel();
			  weakenRuleHeadCand(r, m);
			  solver.pop();
			  solver.push();
			  //LOG("houdini", errs() << "AFTER POP: \n";);
			  //solver.toSmtLib(outs());
		  }
		  solver.pop();
		  solver.push();
	  }
  }

  bool Houdini_Each_Solver_Per_Relation::validateRule(HornRule r, ZSolver<EZ3> &solver)
  {
	  auto &m_hm = m_houdini.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();
	  ExprVector impls;
	  solver.assertions(std::back_inserter(impls));

	  for(ExprVector::iterator it = impls.begin(); it != impls.end(); ++it)
	  {
		  assert(isOpX<IMPL>(*it));
		  Expr tagVar = (*it)->left();
		  Expr tr = (*it)->right();
		  if(tr == extractTransitionRelation(r, db))
		  {
			  solver.assertExpr(tagVar);
		  }
	  }

	  Expr ruleHead_cand_app = m_houdini.getCandidateModel().getDef(r.head());
  	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);
  	  solver.assertExpr(neg_ruleHead_cand_app);

  	  Expr ruleBody = r.body();
  	  ExprVector body_pred_apps;
  	  get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));
  	  for(Expr body_app : body_pred_apps)
	  {
		  solver.assertExpr(m_houdini.getCandidateModel().getDef(body_app)); //add each body predicate app
	  }

  	  //LOG("houdini", errs() << "AFTER PUSH: \n";);
  	  //solver.toSmtLib(errs());
  	  boost::tribool isSat = solver.solve();
  	  if(isSat)
  	  {
  		  LOG("houdini", errs() << "SAT\n";);
  	  	  return SAT_OR_INDETERMIN;
  	  }
  	  else if(!isSat)
  	  {
  		  LOG("houdini", errs() << "UNSAT\n";);
  	  	  return UNSAT;
  	  }
  	  else //if indeterminate
  	  {
  		  LOG("houdini", errs() << "INDETERMINATE\n";);
  		  return SAT_OR_INDETERMIN;
  	  }
  }

  std::map<Expr, ZSolver<EZ3>> Houdini_Each_Solver_Per_Relation::assignEachRelationASolver()
  {
	  auto &m_hm = m_houdini.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();
  	  std::map<Expr, ZSolver<EZ3>> relationToSolverMap;
  	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
  	  {
  		  HornRule r = *it;
  		  Expr ruleHead = r.head();
  		  if(relationToSolverMap.find(ruleHead) != relationToSolverMap.end())
  		  {
  			  ZSolver<EZ3> &solver = relationToSolverMap.find(ruleHead)->second;
  			  Expr var = bind::boolVar(mkTerm<std::string>(std::string("tag2"), ruleHead->efac()));
  			  solver.assertExpr(mk<IMPL>(var, extractTransitionRelation(r, db)));
  			  solver.push();
  		  }
  		  else
  		  {
  			  ZSolver<EZ3> solver(m_hm.getZContext());
  			  Expr tagVar = bind::boolVar(mkTerm<std::string>(std::string("tag"), ruleHead->efac()));
  			  solver.assertExpr(mk<IMPL>(tagVar, extractTransitionRelation(r, db)));
  			  solver.push();
  			  relationToSolverMap.insert(std::make_pair(ruleHead, solver));
  		  }
  	  }
  	  return relationToSolverMap;
  }

  /*
   * Given a rule, weaken its head's candidate
   */
  void HoudiniContext::weakenRuleHeadCand(HornRule r, ZModel<EZ3> m)
  {
	  Expr ruleHead_app = r.head();
	  Expr ruleHead_cand_app = m_houdini.getCandidateModel().getDef(ruleHead_app);

	  LOG("houdini", errs() << "HEAD CAND APP: " << *ruleHead_cand_app << "\n";);

	  if(isOpX<TRUE>(ruleHead_cand_app))
	  {
			return;
	  }
	  if(!isOpX<AND>(ruleHead_cand_app))
	  {
			Expr weaken_cand = mk<TRUE>(ruleHead_cand_app->efac());
			m_houdini.getCandidateModel().addDef(ruleHead_app, weaken_cand);
	  }
	  else
	  {
			ExprVector head_cand_args;
			head_cand_args.insert(head_cand_args.end(), ruleHead_cand_app->args_begin(), ruleHead_cand_app->args_end());
			int num_of_lemmas = head_cand_args.size();

			for(ExprVector::iterator it = head_cand_args.begin(); it != head_cand_args.end(); ++it)
			{
				LOG("houdini", errs() << "EVAL: " << *(m.eval(*it)) << "\n";);
				if(isOpX<FALSE>(m.eval(*it)))
				{
					head_cand_args.erase(it);
					break;
				}
			}

			// This condition can be reached only when the solver answers Indeterminate
			// In this case, we remove an arbitrary lemma (the first one)
			if(head_cand_args.size() == num_of_lemmas)
			{
				LOG("houdini", errs() << "INDETERMINATE REACHED" << "\n");
				head_cand_args.erase(head_cand_args.begin());
			}

			ExprMap bvarToArgMap;
			for(int i=0; i<bind::domainSz(bind::fname(ruleHead_app)); i++)
			{
				Expr arg_i = ruleHead_app->arg(i+1);
				Expr bvar_i = bind::bvar(i, bind::typeOf(arg_i));
				bvarToArgMap.insert(std::make_pair(bvar_i, arg_i));
			}

			if(head_cand_args.size() > 1)
			{
				Expr weaken_cand = mknary<AND>(head_cand_args.begin(), head_cand_args.end());
				Expr weaken_cand_app = replace(weaken_cand, bvarToArgMap);
				m_houdini.getCandidateModel().addDef(ruleHead_app, weaken_cand_app);
			}
			else
			{
				Expr weaken_cand = head_cand_args[0];
				Expr weaken_cand_app = replace(weaken_cand, bvarToArgMap);
				m_houdini.getCandidateModel().addDef(ruleHead_app, weaken_cand_app);
			}
	  }
	  LOG("houdini", errs() << "HEAD AFTER WEAKEN: " << *(m_houdini.getCandidateModel().getDef(ruleHead_app)) << "\n";);
  }

  /*
   * Given a rule head, extract all rules using it in body, then add all such rules to the end of workList
   */
  void HoudiniContext::addUsedRulesBackToWorkList(HornClauseDBWto &db_wto, std::list<HornRule> &workList, HornRule r)
  {
	  auto &m_hm = m_houdini.getHornifyModule();
	  auto &db = m_hm.getHornClauseDB();
  	  Expr ruleHead_app = r.head();
  	  Expr ruleHead_rel = bind::fname(ruleHead_app);

  	  for(Expr fdecl : boost::make_iterator_range(db_wto.heads_begin(ruleHead_rel), db_wto.heads_end(ruleHead_rel)))
  	  {
  		  //LOG("houdini", errs() << "[USEFUL PRED]: " << *fdecl << "\n";);
  		  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it!=db.getRules().end(); ++it)
  		  {
  			  if(*it == r)
  			  {
  				  continue;
  			  }
  			  if(bind::fname((*it).head()) == fdecl)
  			  {
  				  LOG("houdini", errs() << "[NEED RULE]: " << *((*it).head()) << " <===== " << *((*it).body()) << "\n";);
  				  if(std::find(workList.begin(), workList.end(), *it) == workList.end())
  				  {
  					  workList.push_back(*it);
  				  }
  			  }
  		  }
  	  }
  }

  void Houdini::generatePositiveWitness(std::map<Expr, ExprVector> &relationToPositiveStateMap)
  {
	  auto &db = m_hm.getHornClauseDB();
	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
	  {
		  HornRule r = *it;
		  ExprVector body_pred_list;
		  get_all_pred_apps(r.body(), db, std::back_inserter(body_pred_list));
		  if(body_pred_list.size() == 0) // this rule doesn't have predicates in its body.
		  {
			  getRuleHeadState(relationToPositiveStateMap, r, mk<TRUE>(r.head()->efac()));
		  }
	  }
	  LOG("houdini", errs() << "THE WHOLE STATE MAP:\n";);
	  for(std::map<Expr, ExprVector>::iterator itr = relationToPositiveStateMap.begin(); itr != relationToPositiveStateMap.end(); ++itr)
	  {
		  LOG("houdini", errs() << "KEY: " << *(itr->first) << "\n";);
		  LOG("houdini", errs() << "VALUE: [";);
		  for(ExprVector::iterator itr2 = itr->second.begin(); itr2 != itr->second.end(); ++itr2)
		  {
			  LOG("houdini", errs() << *(*itr2) << ", ";);
		  }
		  LOG("houdini", errs() << "]\n";);
	  }
  }

  void Houdini::getReachableStates(std::map<Expr, ExprVector> &relationToPositiveStateMap, Expr from_pred, Expr from_pred_state)
  {
	  auto &db = m_hm.getHornClauseDB();
	  LOG("houdini", errs() << "COME IN\n";);
	  for(HornClauseDB::RuleVector::iterator itr = db.getRules().begin(); itr != db.getRules().end(); ++itr)
	  {
		  HornRule r = *itr;
		  ExprVector body_preds;
		  get_all_pred_apps(r.body(), db, std::back_inserter(body_preds));
		  LOG("houdini", errs() << "BODY PRED SIZE: " << body_preds.size() << "\n";);
		  if(body_preds.size() > 0)
		  {
			  LOG("houdini", errs() << "BODY PRED 0: " << *(body_preds[0]) << "\n";);
			  LOG("houdini", errs() << "FROM PRED: " << *from_pred << "\n";);
		  }
		  if(body_preds.size() == 1 && bind::fname(body_preds[0]) == bind::fname(from_pred))
		  {
			  getRuleHeadState(relationToPositiveStateMap, r, from_pred_state);
		  }
	  }
  }

  void Houdini::getRuleHeadState(std::map<Expr, ExprVector> &relationToPositiveStateMap, HornRule r, Expr from_pred_state)
  {
		LOG("houdini", errs() << "RULE HEAD: " << *(r.head()) << "\n";);
		LOG("houdini", errs() << "RULE BODY: " << *(r.body()) << "\n";);
		auto &db = m_hm.getHornClauseDB();
		ZSolver<EZ3> solver(m_hm.getZContext());
		solver.assertExpr(from_pred_state);
		solver.assertExpr(extractTransitionRelation(r, db));
		solver.toSmtLib(outs());
		boost::tribool isSat = solver.solve();
		if(isSat)
		{
		  LOG("houdini", errs() << "SAT\n";);
		  if(bind::domainSz(bind::fname(r.head())) == 0) //reach a predicate with empty signature. Error state.
		  {
			  LOG("houdini", errs() << "BAD STATE REACHED!\n";);
			  return;
		  }
		  ZModel<EZ3> model = solver.getModel();
		  ExprVector equations;
		  for(int i=0; i<=bind::domainSz(r.head()); i++)
		  {
			  Expr var = bind::domainTy(r.head(), i);
			  Expr value = model.eval(var);
			  LOG("houdini", errs() << "VAR: " << *var << "\n";);
			  LOG("houdini", errs() << "VALUE: " << *value << "\n";);
			  equations.push_back(mk<EQ>(var, value));
		  }
		  Expr state_assignment;
		  if(equations.size() > 1)
		  {
			  state_assignment = mknary<AND>(equations.begin(), equations.end());
		  }
		  else
		  {
			  state_assignment = equations[0];
		  }
		  LOG("houdini", errs() << "STATE ASSIGNMENT: " << *state_assignment << "\n";);

		  if(relationToPositiveStateMap.find(bind::fname(r.head())) == relationToPositiveStateMap.end())
		  {
			  ExprVector states;
			  states.push_back(state_assignment);
			  relationToPositiveStateMap.insert(std::make_pair(bind::fname(r.head()), states));
		  }
		  else
		  {
			  ExprVector &states = relationToPositiveStateMap.find(bind::fname(r.head()))->second;
			  states.push_back(state_assignment);
		  }
		  /*LOG("houdini", errs() << "STATE MAP:\n";);
		  for(std::map<Expr, ExprVector>::iterator itr = relationToPositiveStateMap.begin(); itr != relationToPositiveStateMap.end(); ++itr)
		  {
			  LOG("houdini", errs() << "KEY: " << *(itr->first) << "\n";);
			  LOG("houdini", errs() << "VALUE: [";);
			  for(ExprVector::iterator itr2 = itr->second.begin(); itr2 != itr->second.end(); ++itr2)
			  {
				  LOG("houdini", errs() << *(*itr2) << ", ";);
			  }
			  LOG("houdini", errs() << "]\n";);
		  }*/
		  getReachableStates(relationToPositiveStateMap, r.head(), state_assignment);
		}
		else
		{
		  LOG("houdini", errs() << "UNSAT\n";);
		  return;
		}
  }

}
