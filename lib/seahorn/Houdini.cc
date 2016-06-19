#include "seahorn/Houdini.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "ufo/Expr.hpp"
#include <vector>

using namespace llvm;

namespace seahorn
{
  char Houdini::ID = 0;
  bool Houdini::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();

    //load the Horn clause database
    auto &db = hm.getHornClauseDB ();
    db.buildIndexes ();

    //print DB
  }

  void Houdini::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  void Houdini::printDB (const HornClauseDB &db)
  {
    outs () << db << "\n";
  }

  void Houdini::printHello ()
  {
    outs () << "Hello there.\n";
  }

  Expr Houdini::guessCandidate(Expr fdecl)
  {
	std::vector<Expr> bvars;
	std::vector<Expr> bins;

	//assert (bind::isFapp (pred));
	//Expr fdecl = bind::fname(pred);

	//unsigned idx = 0;
	int i = 0;
	for (i=0; i < bind::domainSz(fdecl); i++)
	{
		if (bind::isIntConst(bind::domainTy(fdecl, i)) || bind::isIntVar(bind::domainTy(fdecl, i)) )
		{
			Expr bvar = bind::bvar (i, bind::typeOf(fdecl));
			bvars.push_back(bvar);
			bvar_map.insert(std::pair<Expr, int>(bvar, i));
			//idx++;
		}
	}
	for (int j=0; j < i; j++)
	{
		for (int k=j; k < i ; k++)
		{
			Expr lt = mk<LT>(bvars[j], bvars[k]);
			bins.push_back(lt);
		}
	}
	Expr conjunction = mknary<AND>(bins.begin(), bins.end());
	return conjunction;
  }

  #define SAT true
  #define UNSAT false

  void Houdini::workListAlgo(HornClauseDB &db)
  {
	  auto &workList = db.getRules();
	  while (!workList.empty())
	  {
		  HornRule r = workList.front();

		  //generate candidate for rule head
		  Expr head_app = r.head();
		  Expr head_pred = bind::fname(head_app);
		  Expr head_cand = guessCandidate(head_pred);

		  //cand is the overall conjunction
		  Expr cand = mk<NEG>(head_cand);

		  //apply head_cand to actual arguments
		  ExprMap head_bvar_map;
		  for (auto itr = head_cand->args_begin (), end = head_cand->args_end (); itr != end; ++itr)
		  {
			  if(bind::isBVar(*itr))
			  {
				  int bvar_id = bind::bvarId(*itr);
				  Expr head_app_arg = bind::domainTy(head_app, bvar_id);// To improve
				  head_bvar_map.insert(std::pair<Expr,Expr>(*itr, head_app_arg));
			  }
		  }

		  /*for(Expr head_cand_arg : head_cand->args)
		  {
			  if(bind::isBvar(head_cand_arg))
			  {
				  int bvar_id = bind::bvarId(head_cand_arg);
				  Expr head_app_arg = bind::domainTy(head_app, bvar_id);// To improve
				  head_bvar_map.put(head_cand_arg, head_app_arg);
			  }
		  }*/

		  Expr head_cand_app = replace(head_cand, head_bvar_map);

		  //cand_app is application of the overall conjunction
		  Expr cand_app = mk<NEG>(head_cand_app);

		  //generate candidate for rule body
		  Expr body = r.body();
		  ExprMap body_map;
		  for (auto itr = body->args_begin(), end = body->args_end(); itr != end; ++itr)
		  {
			  if(bind::isFapp(*itr))
			  {
				  Expr body_app = *itr;
				  Expr body_pred = bind::fname(body_app);
				  if(bind::isFdecl (body_pred) && db.hasRelation (body_pred)) //fdecl is a predicate
				  {
				  	 Expr body_cand = guessCandidate(body_pred);
				  	 //apply body_cand to actual arguments
				  	 ExprMap body_bvar_map;
				  	 for(auto itr_cand = body_cand->args_begin(), end = body_cand->args_end(); itr_cand != end; ++itr_cand)
				  	 {
				  		 if(bind::isBVar(*itr_cand))
				  		 {
				  			 int bvar_id = bind::bvarId(*itr_cand);
				  			 Expr body_app_arg = bind::domainTy(body_app, bvar_id);
				  		     body_bvar_map.insert(std::pair<Expr, Expr>(*itr_cand, body_app_arg));
				  		 }
				  	 }
				  	 Expr body_cand_app = replace(body_cand, body_bvar_map);
				  	 body_map.insert(std::pair<Expr, Expr>(body_app, body_cand_app));
				  }
			  }
		  }
		  /*for(Expr e : body->args)
		  {
			  if(bind::isFapp(e))
			  {
				  Expr body_app = e;
				  Expr body_pred = bind::fname(body_app);
				  if(bind::isFdecl (body_pred) && db.hasRelation (body_pred)) //fdecl is a predicate
				  {
					  body_cand = guessCandidate(body_pred);
					  //apply body_cand to actual arguments
					  ExprMap body_bvar_map;
					  for(Expr body_cand_arg : body_cand->args)
					  {
						  if(bind::isBvar(body_cand_arg))
						  {
							  int bvar_id = bind::bvarId(body_cand_arg);
							  Expr body_app_arg = bind::domainTy(body_app, bvar_id);
							  body_bvar_map.put(body_cand_arg, body_app_arg);
						  }
					  }
					  Expr body_cand_app = replace(body_cand, body_bvar_map);
					  body_map.put(body_app, body_cand_app);
				  }
			  }
		  }*/
		  Expr new_body = replace(body, body_map);

		  //update cand and cand_app
		  cand_app = mk<AND>(cand_app, new_body);

		  if(validateRule(cand_app) == SAT)
		  {
			  //weaken candidate for r.head(), how ?


			  //add rules in db.use(r.head()) to worklist
			  Expr head_app = r.head();
			  for(auto r_use : db.use(head_app))
			  {
				  workList.push_back(*r_use);
			  }
		  }
		  else // the ret is UNSAT
		  {
		      workList.erase(workList.begin());
		  }
	  }
  }

  bool Houdini::validateRule(Expr cand_app)
  {
	  outs() << cand_app << "\n";
	  // should call smt solver
	  return UNSAT;
  }
}
  /*
   * abandoned function
   */
  /*bool Houdini::validate_OldVersion(HornRule r, HornClauseDB &db)
  {
	  //extract predicates from rule head and rule body
	  Expr head_app = r.head ();
	  Expr head_pred = bind::fname(head_app);

	  ExprMap map;
	  Expr head_cand = guessCandidate(head_pred);
	  for (Expr arg : head_cand->args)
	  {
		  if(bind::isBvar(arg))
		  {
			  int bvar_id = bind::bvarId(arg);
			  // bvar_id = bvar_map.get(arg);
			  Expr app_arg = bind::domainTy(head_app, bvar_id);
			  map.put(arg, app_arg);
		  }
	  }
	  Expr head_cand_app = replace(head_cand, map);

	  ExprVector body_preds;
	  r.used_relations (db, std::back_inserter (body_preds));

	  //for each predicate, generate a candidate
	  for(Expr pred : body_preds)
	  {
		  Expr cand = guessCandidate(pred);
		  Expr map;
		  for(Expr arg : cand->args)
		  {
			  if(bind::isBvar(arg))
			  {
				  int bvar_id = bvarId(arg);
				  //Expr app_arg = bind::domainTy(pred, bvar_id);
				  //map.put(arg, app_arg);
			  }
		  }

	  }

	  //find the variables that the predicate apply on
	  //apply candidates to these variables.
    return true;
  }
}*/
