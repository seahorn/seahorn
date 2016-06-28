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

using namespace llvm;

namespace seahorn
{
  char Houdini::ID = 0;

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

  bool Houdini::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    //load the Horn clause database
    auto &db = hm.getHornClauseDB ();
    db.buildIndexes ();

    runHoudini(db, hm);

    return false;
  }

  void Houdini::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  /*
   * Use template to convert a predicate to candidate
   */
  Expr Houdini::relToCand(Expr fdecl)
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

  #define SAT true
  #define UNSAT false

  std::map<Expr, Expr> Houdini::currentCandidates;	//a map from predicates to candidates

  /*
   * Build the map from predicates to candidates
   */
  void Houdini::guessCandidate(HornClauseDB &db)
  {
	  for(Expr rel : db.getRelations())
	  {
		  if(bind::isFdecl(rel))
		  {
			  Expr cand = relToCand(rel);
			  currentCandidates.insert(std::pair<Expr, Expr>(rel, cand));
		  }
	  }
  }

  /*
   * Main loop of Houdini algorithm
   */
  void Houdini::runHoudini(HornClauseDB &db, HornifyModule &hm)
  {
	  guessCandidate(db);

	  HornClauseDB::RuleVector workList;
	  workList.insert(workList.end(), db.getRules().begin(), db.getRules().end());

	  while(!workList.empty())
	  {
		  HornRule r = workList.front();
		  errs() << "RULE HEAD: " << *(r.head()) << "\n";
		  errs() << "RULE BODY: " << *(r.body()) << "\n";
		  while (validateRule(r, db, hm) == SAT)
		  {
			  workList = addUsedRulesBackToWorkList(db, workList, r.head());
			  weakenRuleHeadCand(r);
		  }
		  workList.erase(workList.begin());
	  }
  }

  /*
   * Given a rule, check if it's validate
   */
  bool Houdini::validateRule(HornRule r, HornClauseDB &db, HornifyModule &hm)
  {
	  Expr ruleHead_cand_app = applyActualArgsToCand(r.head());
	  Expr neg_ruleHead_cand_app = mk<NEG>(ruleHead_cand_app);

	  Expr ruleBody = r.body();
	  ExprMap body_map;
	  ExprVector body_pred_apps;
	  get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));

	  for(ExprVector::iterator itr = body_pred_apps.begin(); itr != body_pred_apps.end(); ++itr)
	  {
		  body_map.insert(std::pair<Expr, Expr>(*itr, applyActualArgsToCand(*itr)));
	  }

	  Expr body_cand_app = replace(ruleBody, body_map);

	  Expr whole_cand = mk<AND>(neg_ruleHead_cand_app, body_cand_app);

	  errs() << "WHOLE CANDIDATE: " << *whole_cand << "\n";

	  ZSolver<EZ3> solver(hm.getZContext ());
	  solver.assertExpr(whole_cand);
	  solver.toSmtLib(errs());
	  bool isSat = solver.solve();
	  if(isSat)
	  {
		  errs() << "SAT\n";
	  }
	  else
	  {
	  	  errs() << "UNSAT\n";
	  }
	  return isSat;
  }

  /*
   * Given a function application, apply its actual arguments to its candidate
   */
  Expr Houdini::applyActualArgsToCand(Expr fapp)
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
	  Expr cand_app = replace(cand, bvar_map);
	  return cand_app;
  }

  /*
   * Given a rule, weaken its head's candidate
   */
  void Houdini::weakenRuleHeadCand(HornRule r)
  {
	  Expr ruleHead_app = r.head();
	  Expr ruleHead_rel = bind::fname(ruleHead_app);
	  Expr ruleHead_cand = currentCandidates[ruleHead_rel];

	  if(isOpX<TRUE>(ruleHead_cand))
	  {
	  		return;
	  }
	  if(!isOpX<AND>(ruleHead_cand))
	  {
	  		Expr weaken_cand = mk<TRUE>(ruleHead_cand->efac());
	  		currentCandidates[ruleHead_rel] = weaken_cand;
	  }
	  else
	  {
	  		ExprVector head_cand_args;
	  		head_cand_args.insert(head_cand_args.end(), ruleHead_cand->args_begin(), ruleHead_cand->args_end());
	  		head_cand_args.erase(head_cand_args.begin());

	  		if(head_cand_args.size() > 1)
	  		{
	  			Expr weaken_cand = mknary<AND>(head_cand_args.begin(), head_cand_args.end());
	  			currentCandidates[ruleHead_rel] = weaken_cand;
	  		}
	  		else
	  		{
	  			Expr weaken_cand = head_cand_args[0];
	  			currentCandidates[ruleHead_rel] = weaken_cand;
	  		}
	  }
  }

  /*
   * Given a rule head, extract all rules using it in body, then add all such rules to the end of workList
   */
  HornClauseDB::RuleVector Houdini::addUsedRulesBackToWorkList(HornClauseDB &db, HornClauseDB::RuleVector workList, Expr ruleHead_app)
  {
	  Expr ruleHead_rel = bind::fname(ruleHead_app);
	  for(auto r_use : db.use(ruleHead_rel))
	  {
		  bool isExist = false;
		  for(HornClauseDB::RuleVector::iterator itr=workList.begin(); itr!=workList.end(); ++itr)
		  {
			  if(*itr == *r_use)
			  {
				  isExist = true;
				  break;
			  }
		  }
		  if(isExist == false)
		  {
			  workList.push_back(*r_use);
		  }
	  }
	  return workList;
  }
}
