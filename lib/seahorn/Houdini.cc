#include "seahorn/Houdini.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"
#include <vector>
#include <boost/logic/tribool.hpp>
#include "seahorn/HornClauseDBWto.hh"
#include <algorithm>

#include "ufo/Stats.hh"

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
    houdini.setInitialCandidatesSet(GuessCandidates::guessCandidates(hm.getHornClauseDB()));
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

  /*GuessCandidates methods begin*/

  /*
   * Use simple template to convert a predicate to candidate
   */
  Expr GuessCandidates::relToCand(Expr fdecl)
  {
	ExprVector bvars;
	ExprVector bins;   // a vector of LT expressions
	Expr cand = NULL;

	int bvar_count = 0;
	unsigned i = 0;
	for (i=0; i < bind::domainSz(fdecl); i++)
	{
		// if its type is INT
		if (isOpX<INT_TY>(bind::domainTy(fdecl, i)))
		{
			// what is efac?
			Expr bvar = bind::bvar (i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac())); //the id of bvar is the same as related arg index
			bvars.push_back(bvar);
			bvar_count ++;
		}
	}

	//What if there's no bvar?
	if(bvar_count == 0)
	{
		cand = mk<TRUE>(fdecl->efac());
	}
	// if there is only one bvar, create a int constant and make an lt expr
	else if(bvar_count == 1)
	{
		Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
		cand = mk<LT>(bvars[0], zero);
	}
	// if there are more than two bvars, make an lt expr
	else if(bvar_count == 2)
	{
		Expr lt1 = mk<LT>(bvars[0], bvars[1]);
		Expr lt2 = mk<LT>(bvars[1], bvars[0]);
		bins.push_back(lt1);
		bins.push_back(lt2);

		cand = mknary<AND>(bins.begin(), bins.end());
		//cand = mk<LT>(bvars[0], bvars[1]);
	}
	else // bvar_count > 2
	{
		for(int j=0; j<bvars.size()-1; j++)
		{
			Expr lt = mk<LT>(bvars[j], bvars[j+1]);
			bins.push_back(lt);
		}
		cand = mknary<AND>(bins.begin(), bins.end());
	}

	return cand;
  }

  /*
   * Use complex templates to convert a predicate to candidate
   */
  Expr GuessCandidates::applyComplexTemplates(Expr fdecl)
  {
	ExprVector bvars;
	ExprVector conjuncts;   // a vector of conjuncts
	ExprVector disjuncts;
	Expr cand = NULL;

	int bvar_count = 0;
	unsigned i = 0;
	for (i=0; i < bind::domainSz(fdecl); i++)
	{
		// if its type is INT
		if (isOpX<INT_TY>(bind::domainTy(fdecl, i)))
		{
			// what is efac?
			Expr bvar = bind::bvar (i, mk<INT_TY>(bind::domainTy(fdecl, i)->efac())); //the id of bvar is the same as related arg index
			bvars.push_back(bvar);
			bvar_count ++;
		}
	}

	if(bvar_count == 0)
	{
		cand = mk<TRUE>(fdecl->efac());
	}
	else if(bvar_count == 1)
	{
		generateLemmasForOneBvar(bvars[0], conjuncts);
		cand = mknary<AND>(conjuncts.begin(), conjuncts.end());
	}
	else if(bvar_count == 2)
	{
		generateLemmasForOneBvar(bvars[0], conjuncts);
		generateLemmasForOneBvar(bvars[1], conjuncts);

		Expr lt1 = mk<LEQ>(bvars[0], bvars[1]);
		//Expr lt2 = mk<LEQ>(bvars[1], bvars[0]);
		conjuncts.push_back(lt1);
		//conjuncts.push_back(lt2);

		cand = mknary<AND>(conjuncts.begin(), conjuncts.end());
	}
	else // bvar_count > 2
	{
		generateLemmasForOneBvar(bvars[0], conjuncts);
		for(int j=0; j<bvars.size()-1; j++)
		{
			generateLemmasForOneBvar(bvars[j+1], conjuncts);
			Expr lt = mk<LEQ>(bvars[j], bvars[j+1]);
			conjuncts.push_back(lt);
		}
		cand = mknary<AND>(conjuncts.begin(), conjuncts.end());
	}

	return cand;
  }

  void GuessCandidates::generateLemmasForOneBvar(Expr bvar, ExprVector &conjuncts)
  {
	  Expr zero = mkTerm<mpz_class> (0, bvar->efac());
	  Expr one = mkTerm<mpz_class> (1, bvar->efac());
	  Expr minusOne = mkTerm<mpz_class> (-1, bvar->efac());
	  conjuncts.push_back(mk<LEQ>(bvar, zero));
	  //conjuncts.push_back(mk<GEQ>(bvar, zero));
	  conjuncts.push_back(mk<LEQ>(bvar, one));
	  //conjuncts.push_back(mk<GEQ>(bvar, one));
	  conjuncts.push_back(mk<LEQ>(bvar, minusOne));
	  //conjuncts.push_back(mk<GEQ>(bvar, minusOne));
  }

  /*
   * Build the map from predicates to candidates
   */
  std::map<Expr, Expr> GuessCandidates::guessCandidates(HornClauseDB &db)
  {
	  std::map<Expr, Expr> candidates;
	  for(Expr rel : db.getRelations())
	  {
		  if(bind::isFdecl(rel))
		  {
			  Expr cand = relToCand(rel);
			  //Expr cand = applyComplexTemplates(rel);
			  candidates.insert(std::pair<Expr, Expr>(rel, cand));
		  }
	  }
	  return candidates;
  }

  /*GuessCandidates methods end*/

  /*Houdini methods begin*/

  struct IsBVar : public std::unary_function<Expr, bool>
  {
	   IsBVar () {}
	   bool operator() (Expr e)
	   {return bind::isBVar (e);}
  };

  struct IsPredApp : public std::unary_function<Expr, bool>
  {
	   HornClauseDB &m_db;
	   IsPredApp (HornClauseDB &db) : m_db (db) {}

	   bool operator() (Expr e)
	   {return bind::isFapp (e) && m_db.hasRelation (bind::fname(e));}
  };

  /*
   * Extract all bvars in an expression
   */
  template<typename OutputIterator>
  void Houdini::get_all_bvars (Expr e, OutputIterator out)
  {filter (e, IsBVar(), out);}

  /*
   * Extract all predicates in an expression
   */
  template<typename OutputIterator>
  void Houdini::get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out)
  {filter (e, IsPredApp(db), out);}

  //std::map<Expr, Expr> Houdini::currentCandidates;	//a map from predicates to candidates

  void Houdini::addInvarCandsToProgramSolver()
  {
	  auto &db = m_hm.getHornClauseDB();
	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
	  {
			HornRule r = *it;
			Expr rhead_app = r.head();
			Expr rhead_cand_app = fAppToCandApp(rhead_app);
			LOG("candidates", errs() << "HEAD: " << *rhead_app << "\n";);
			LOG("candidates", errs() << "CAND: " << *rhead_cand_app << "\n";);
			if(!isOpX<TRUE>(rhead_cand_app))
			{
				LOG("candidates", errs() << "ADD CONSTRAINT\n";);
				db.addConstraint(rhead_app, rhead_cand_app);
			}
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

	  LOG("houdini", errs() << "CAND MAP:\n";);
	  LOG("houdini", errs() << "MAP SIZE: " << currentCandidates.size() << "\n";);
	  for(std::map<Expr, Expr>::iterator it = currentCandidates.begin(); it!= currentCandidates.end(); ++it)
	  {
		LOG("houdini", errs() << "PRED: " << *(it->first) << "\n";);
		LOG("houdini", errs() << "CAND: " << *(it->second) << "\n";);
	  }

	  std::list<HornRule> workList;
	  workList.insert(workList.end(), db.getRules().begin(), db.getRules().end());
	  workList.reverse();

	  if (config == EACH_RULE_A_SOLVER)
	  {
		  Houdini_Each_Solver_Per_Rule houdini_solver_per_rule(*this, db, m_hm, db_wto, workList);
		  houdini_solver_per_rule.run();
	  }
	  else if (config == EACH_RELATION_A_SOLVER)
	  {
		  Houdini_Each_Solver_Per_Relation houdini_solver_per_relation(*this, db, m_hm, db_wto, workList);
		  houdini_solver_per_relation.run();
	  }
	  else if (config == NAIVE)
	  {
		  Houdini_Naive houdini_naive(*this, db, m_hm, db_wto, workList);
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
  			  addUsedRulesBackToWorkList(m_db, m_db_wto, m_workList, r);
  			  ZModel<EZ3> m = m_solver.getModel();
  			  weakenRuleHeadCand(r, m);
  		  }
  	  }
  }

  bool Houdini_Naive::validateRule(HornRule r, ZSolver<EZ3> &solver)
  {
	  solver.reset();

	  Expr ruleHead_cand_app = m_houdini.fAppToCandApp(r.head());
	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);
	  solver.assertExpr(neg_ruleHead_cand_app);

	  Expr ruleBody = r.body();
	  ExprVector body_pred_apps;
	  m_houdini.get_all_pred_apps(ruleBody, m_db, std::back_inserter(body_pred_apps));
	  for(ExprVector::iterator itr = body_pred_apps.begin(); itr != body_pred_apps.end(); ++itr)
	  {
		  solver.assertExpr(m_houdini.fAppToCandApp(*itr)); //add each body predicate app
	  }

	  solver.assertExpr(m_houdini.extractTransitionRelation(r, m_db));

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
			  addUsedRulesBackToWorkList(m_db, m_db_wto, m_workList, r);
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

  	  Expr ruleHead_cand_app = m_houdini.fAppToCandApp(r.head());
  	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);
  	  solver.assertExpr(neg_ruleHead_cand_app);

  	  Expr ruleBody = r.body();
  	  ExprVector body_pred_apps;
  	  m_houdini.get_all_pred_apps(ruleBody, m_db, std::back_inserter(body_pred_apps));
  	  for(ExprVector::iterator itr = body_pred_apps.begin(); itr != body_pred_apps.end(); ++itr)
  	  {
  		  solver.assertExpr(m_houdini.fAppToCandApp(*itr)); //add each body predicate app
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

  std::map<HornRule, ZSolver<EZ3>> Houdini_Each_Solver_Per_Rule::assignEachRuleASolver(HornClauseDB &db, HornifyModule &hm)
  {
  	  std::map<HornRule, ZSolver<EZ3>> ruleToSolverMap;
  	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
  	  {
  		  HornRule r = *it;
  		  Expr tr = m_houdini.extractTransitionRelation(r, db);
  		  ZSolver<EZ3> solver(hm.getZContext());
  		  solver.assertExpr(tr);
  		  solver.push();

  		  ruleToSolverMap.insert(std::pair<HornRule, ZSolver<EZ3>>(r, solver));
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
			  addUsedRulesBackToWorkList(m_db, m_db_wto, m_workList, r);
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
	  ExprVector impls;
	  solver.assertions(std::back_inserter(impls));

	  for(ExprVector::iterator it = impls.begin(); it != impls.end(); ++it)
	  {
		  assert(isOpX<IMPL>(*it));
		  Expr tagVar = (*it)->left();
		  Expr tr = (*it)->right();
		  if(tr == m_houdini.extractTransitionRelation(r, m_db))
		  {
			  solver.assertExpr(tagVar);
		  }
	  }

  	  Expr ruleHead_cand_app = m_houdini.fAppToCandApp(r.head());
  	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);
  	  solver.assertExpr(neg_ruleHead_cand_app);

  	  Expr ruleBody = r.body();
  	  ExprVector body_pred_apps;
  	  m_houdini.get_all_pred_apps(ruleBody, m_db, std::back_inserter(body_pred_apps));
  	  for(ExprVector::iterator itr = body_pred_apps.begin(); itr != body_pred_apps.end(); ++itr)
  	  {
  		  solver.assertExpr(m_houdini.fAppToCandApp(*itr)); //add each body predicate app
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

  std::map<Expr, ZSolver<EZ3>> Houdini_Each_Solver_Per_Relation::assignEachRelationASolver(HornClauseDB &db, HornifyModule &hm)
  {
  	  std::map<Expr, ZSolver<EZ3>> relationToSolverMap;
  	  for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
  	  {
  		  HornRule r = *it;
  		  Expr ruleHead = r.head();
  		  if(relationToSolverMap.find(ruleHead) != relationToSolverMap.end())
  		  {
  			  ZSolver<EZ3> &solver = relationToSolverMap.find(ruleHead)->second;
  			  Expr var = bind::boolVar(mkTerm<std::string>(std::string("tag2"), ruleHead->efac()));
  			  solver.assertExpr(mk<IMPL>(var, m_houdini.extractTransitionRelation(r, db)));
  			  solver.push();
  		  }
  		  else
  		  {
  			  ZSolver<EZ3> solver(hm.getZContext());
  			  Expr tagVar = bind::boolVar(mkTerm<std::string>(std::string("tag"), ruleHead->efac()));
  			  solver.assertExpr(mk<IMPL>(tagVar, m_houdini.extractTransitionRelation(r, db)));
  			  solver.push();
  			  relationToSolverMap.insert(std::pair<Expr, ZSolver<EZ3>>(ruleHead, solver));
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
	  Expr ruleHead_rel = bind::fname(ruleHead_app);
	  Expr ruleHead_cand = m_houdini.getCurrentCandidates()[ruleHead_rel];

	  LOG("houdini", errs() << "HEAD CAND APP: " << *(m_houdini.applyArgsToBvars(ruleHead_cand, ruleHead_app)) << "\n";);

	  if(isOpX<TRUE>(ruleHead_cand))
	  {
			return;
	  }
	  if(!isOpX<AND>(ruleHead_cand))
	  {
			Expr weaken_cand = mk<TRUE>(ruleHead_cand->efac());
			m_houdini.getCurrentCandidates()[ruleHead_rel] = weaken_cand;
	  }
	  else
	  {
			ExprVector head_cand_args;
			head_cand_args.insert(head_cand_args.end(), ruleHead_cand->args_begin(), ruleHead_cand->args_end());
			int num_of_lemmas = head_cand_args.size();

			for(ExprVector::iterator it = head_cand_args.begin(); it != head_cand_args.end(); ++it)
			{
				LOG("houdini", errs() << "EVAL: " << *(m.eval(m_houdini.applyArgsToBvars(*it, ruleHead_app))) << "\n";);
				if(isOpX<FALSE>(m.eval(m_houdini.applyArgsToBvars(*it, ruleHead_app))))
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

			if(head_cand_args.size() > 1)
			{
				Expr weaken_cand = mknary<AND>(head_cand_args.begin(), head_cand_args.end());
				m_houdini.getCurrentCandidates()[ruleHead_rel] = weaken_cand;
			}
			else
			{
				Expr weaken_cand = head_cand_args[0];
				m_houdini.getCurrentCandidates()[ruleHead_rel] = weaken_cand;
			}
	  }
	  LOG("houdini", errs() << "HEAD AFTER WEAKEN: " << *(m_houdini.getCurrentCandidates()[ruleHead_rel]) << "\n";);
  }

  /*
   * Given a rule head, extract all rules using it in body, then add all such rules to the end of workList
   */
  void HoudiniContext::addUsedRulesBackToWorkList(HornClauseDB &db, HornClauseDBWto &db_wto, std::list<HornRule> &workList, HornRule r)
  {
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

  /*
   * Given a function application, apply its actual arguments to its candidate
   */
  Expr Houdini::fAppToCandApp(Expr fapp)
  {
	  Expr fdecl = bind::fname(fapp);
	  Expr cand = currentCandidates[fdecl];
	  return applyArgsToBvars(cand, fapp);
  }

  /*
   * apply function arguments to any lemma of it.
   */
  Expr Houdini::applyArgsToBvars(Expr cand, Expr fapp)
  {
 	  ExprMap bvar_map = getBvarsToArgsMap(fapp);
 	  return replace(cand, bvar_map);
  }

  ExprMap Houdini::getBvarsToArgsMap(Expr fapp)
  {
	  Expr fdecl = bind::fname(fapp);
	  Expr cand = currentCandidates[fdecl];

	  ExprMap bvar_map;
	  ExprVector bvars;
	  get_all_bvars(cand, std::back_inserter(bvars));

	  for(ExprVector::iterator it = bvars.begin(); it != bvars.end(); ++it)
	  {
		  unsigned bvar_id = bind::bvarId(*it);
		  Expr app_arg = bind::domainTy(fapp, bvar_id);// To improve
		  bvar_map.insert(std::pair<Expr,Expr>(*it, app_arg));
	  }
	  return bvar_map;
  }

  Expr Houdini::extractTransitionRelation(HornRule r, HornClauseDB &db)
  {
	  Expr ruleBody = r.body();
	  ExprMap body_map;
	  ExprVector body_pred_apps;
	  get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));

	  for(ExprVector::iterator itr = body_pred_apps.begin(); itr != body_pred_apps.end(); ++itr)
	  {
		  body_map.insert(std::pair<Expr, Expr>(*itr, mk<TRUE>((*itr)->efac())));
	  }

	  Expr body_constraints = replace(ruleBody, body_map);
	  return body_constraints;
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
			  relationToPositiveStateMap.insert(std::pair<Expr, ExprVector>(bind::fname(r.head()), states));
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
