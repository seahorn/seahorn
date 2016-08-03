#include "seahorn/PredicateAbstraction.hh"
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
	char PredicateAbstraction::ID = 0;

	std::map<Expr, int> PredicateAbstraction::predToBiNumMap;
    std::map<Expr, Expr> PredicateAbstraction::oldToNewPredMap;
    std::map<Expr, Expr> PredicateAbstraction::currentCandidates;

	bool PredicateAbstraction::runOnModule (Module &M)
	{
		HornifyModule &hm = getAnalysis<HornifyModule> ();

		//load the Horn clause database
		auto &db = hm.getHornClauseDB ();
		db.buildIndexes ();

		//guess candidates
		guessCandidate(db);

		//run main algorithm
		HornClauseDB new_db = runOnDB(db);

		//initialize spacer based on new DB
		m_fp.reset (new ZFixedPoint<EZ3> (hm.getZContext ()));
		ZFixedPoint<EZ3> &fp = *m_fp;
		ZParams<EZ3> params (hm.getZContext ());
		params.set (":engine", "spacer");
//		// -- disable slicing so that we can use cover
		params.set (":xform.slice", false);
		params.set (":use_heavy_mev", true);
		params.set (":reset_obligation_queue", true);
		params.set (":pdr.flexible_trace", false);
		params.set (":xform.inline-linear", false);
		params.set (":xform.inline-eager", false);
//		// -- disable utvpi. It is unstable.
		params.set (":pdr.utvpi", false);
//		// -- disable propagate_variable_equivalences in tail_simplifier
		params.set (":xform.tail_simplifier_pve", false);
		params.set (":xform.subsumption_checker", true);
//		params.set (":order_children", true);
//		params.set (":pdr.max_num_contexts", "500");
		fp.set (params);
		new_db.loadZFixedPoint (fp, false);
		boost::tribool result = fp.query ();
//
//		if (result) outs () << "sat";
//		else if (!result) outs () << "unsat";
//		else outs () << "unknown";
//		outs () << "\n";
//
//		printInvars (M);

		return false;
	}

	void PredicateAbstraction::getAnalysisUsage (AnalysisUsage &AU) const
	{
	    AU.addRequired<HornifyModule> ();
	    AU.setPreservesAll();
	}

	HornClauseDB PredicateAbstraction::runOnDB(HornClauseDB &db)
	{
		outs() << "OLD DB: \n";
		outs() << db << "\n";

		HornClauseDB new_DB(db.getExprFactory ());
		int index = 0;

		for(Expr rel : db.getRelations())
		{
			predToBiNumMap.insert(std::pair<Expr, int>(rel, index));
			index++;
		}

		for(Expr rel : db.getRelations())
		{
			outs() << "OLD PRED: " << *rel << "\n";
			ExprVector new_args;
			//Push fdecl name
			new_args.push_back(bind::fname(rel));
			//Push boolean types
			for(int i=0; i < db.getRelations().size(); i++)
			{
				new_args.push_back(mk<BOOL_TY>(rel->efac()));
			}
			new_args.push_back(bind::rangeTy(rel));
			Expr new_rel = mknary<FDECL>(new_args);
			outs() << "NEW PRED: " << *new_rel << "\n";
			new_DB.registerRelation(new_rel);
			oldToNewPredMap.insert(std::pair<Expr, Expr>(rel, new_rel));
		}
		outs() << "NEW DB: \n";
		outs() << new_DB << "\n";

		for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
		{
			HornRule r = *it;
			outs() << "OLD RULE HEAD: " << *(r.head()) << "\n";
			outs() << "OLD RULE BODY: " << *(r.body()) << "\n";

			//Map from predicate apps to bool vars
			std::map<Expr, Expr> predAppToBoolVarMap;

			//Count occurrence time for each relation in per rule
			std::map<Expr, int> relOccurrenceTimesMap;
			ExprVector pred_vector;
			get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
			pred_vector.push_back(r.head());
			for(ExprVector::iterator it = pred_vector.begin(); it!= pred_vector.end(); ++it)
			{
				if(relOccurrenceTimesMap.find(bind::fname(*it)) == relOccurrenceTimesMap.end())
				{
					relOccurrenceTimesMap.insert(std::pair<Expr, int>(bind::fname(*it), 1));
				}
				else
				{
					relOccurrenceTimesMap[bind::fname(*it)] += 1;
				}
			}

			//construct new rule head.
			Expr rule_head = r.head();
			Expr new_rule_head_rel = oldToNewPredMap.find(bind::fname(rule_head))->second;

			ExprVector new_rule_head_args;
			for(std::map<Expr, int>::iterator it = predToBiNumMap.begin(); it != predToBiNumMap.end(); ++it)
			{
				if(it->first == bind::fname(rule_head))
				{
					int occur_num = relOccurrenceTimesMap[bind::fname(rule_head)];
					assert(occur_num >= 1);
					int bool_var_index = it->second;
					std::ostringstream oss;
					oss << "b" << bool_var_index;
					for(int i=0; i<occur_num - 1; i++)
					{
						oss << "\'";
					}
					Expr bi = bind::boolVar(mkTerm<std::string>(oss.str(), db.getExprFactory ()));
					predAppToBoolVarMap.insert(std::pair<Expr, Expr>(rule_head, bi));
					new_rule_head_args.push_back(bi);
				}
				else
				{
					int bool_var_index = it->second;
					std::ostringstream oss;
					oss << "b" << bool_var_index;
					Expr bi = bind::boolVar(mkTerm<std::string>(oss.str(), db.getExprFactory ()));
					new_rule_head_args.push_back(bi);
				}
			}

			Expr new_rule_head = bind::fapp(new_rule_head_rel, new_rule_head_args);
			outs() << "NEW RULE HEAD: " << *new_rule_head << "\n";

			//construct head iff
			Expr rule_head_cand_app = fAppToCandApp(rule_head);
			Expr rule_head_iff = mk<IFF>(predAppToBoolVarMap[rule_head], rule_head_cand_app);
			outs() << "RULE HEAD IFF: " << *rule_head_iff << "\n";

			//construct new body
			ExprVector new_body_exprs;
			new_body_exprs.push_back(rule_head_iff);

			//Record occurence of rel in body, for increasing the number of primes
			std::map<Expr, int> relOccurrenceInBodyMap;

			//For each predicate in the body, construct new version of predicate.
			Expr rule_body = r.body();
			ExprVector body_pred_apps;
			get_all_pred_apps(rule_body, db, std::back_inserter(body_pred_apps));
			for(ExprVector::iterator it = body_pred_apps.begin(); it != body_pred_apps.end(); ++it)
			{
				Expr rule_body_pred = *it;
				assert(oldToNewPredMap.find(bind::fname(rule_body_pred)) != oldToNewPredMap.end());
				Expr new_rule_body_rel = oldToNewPredMap.find(bind::fname(rule_body_pred))->second;

				if(relOccurrenceInBodyMap.find(bind::fname(rule_body_pred)) == relOccurrenceInBodyMap.end())
				{
					relOccurrenceInBodyMap.insert(std::pair<Expr, int>(bind::fname(rule_body_pred), 1));
				}
				else
				{
					relOccurrenceInBodyMap[bind::fname(rule_body_pred)] += 1;
				}

				ExprVector new_rule_body_args;
				//Push boolean variables into arguments of new predicate
				for(std::map<Expr, int>::iterator it = predToBiNumMap.begin(); it != predToBiNumMap.end(); ++it)
				{
					if(it->first == bind::fname(rule_body_pred))
					{
						int occur_num = relOccurrenceInBodyMap[bind::fname(rule_body_pred)];
						assert(occur_num >= 1);
						int bool_var_index = it->second;
						std::ostringstream oss;
						oss << "b" << bool_var_index;
						for(int i=0; i<occur_num - 1; i++)
						{
							oss << "\'";
						}
						Expr bi = bind::boolVar(mkTerm<std::string>(oss.str(), db.getExprFactory ()));
						predAppToBoolVarMap.insert(std::pair<Expr, Expr>(rule_body_pred, bi));
						new_rule_body_args.push_back(bi);
					}
					else
					{
						int bool_var_index = it->second;
						std::ostringstream oss;
						oss << "b" << bool_var_index;
						Expr bi = bind::boolVar(mkTerm<std::string>(oss.str(), db.getExprFactory ()));
						new_rule_body_args.push_back(bi);
					}
				}
				Expr new_rule_body_pred = bind::fapp(new_rule_body_rel, new_rule_body_args);
				new_body_exprs.push_back(new_rule_body_pred);
			}
			//for each predicate in the body, create iff
			for(ExprVector::iterator it = body_pred_apps.begin(); it != body_pred_apps.end(); ++it)
			{
				Expr rule_body_pred = *it;
				Expr rule_body_cand_app = fAppToCandApp(rule_body_pred);
				Expr rule_body_bool_var = predAppToBoolVarMap[rule_body_pred];
				Expr rule_body_iff = mk<IFF>(rule_body_bool_var, rule_body_cand_app);
				new_body_exprs.push_back(rule_body_iff);
			}
			//Extract the constraints
			Expr constraints = extractTransitionRelation(r, db);
			new_body_exprs.push_back(constraints);
			//Construct new body
			Expr new_rule_body = mknary<AND>(new_body_exprs.begin(), new_body_exprs.end());
			outs() << "NEW RULE BODY :" << *new_rule_body << "\n";
			HornRule new_rule(r.vars (), new_rule_head, new_rule_body);
			new_DB.addRule(new_rule);
		}
//		 errs () << "QUERIES 2\n";
//		        for (auto q: db.getQueries ())
//		        	errs () << *q << "\n";

		for(auto old_query : db.getQueries())
		{
			outs() << "OLD QUERY: " << *old_query << "\n";
			Expr old_rel = bind::fname(old_query);
			outs() << "OLD REL: " << *old_rel << "\n";
			Expr new_rel = oldToNewPredMap.find(old_rel)->second;
			outs() << "NEW REL: " << *new_rel << "\n";
			ExprVector new_args;
			for(int i=0; i<oldToNewPredMap.size(); i++)
			{
				std::ostringstream oss;
				oss << "b" << i;
				Expr bi = bind::boolVar(mkTerm<std::string>(oss.str(), db.getExprFactory ()));
				new_args.push_back(bi);
			}
			Expr new_query = bind::fapp(new_rel, new_args);
			outs() << "NEW QUERY: " << *new_query << "\n";
			new_DB.addQuery(new_query);
		}

		outs() << "NEW DB: \n";
		outs() << new_DB << "\n";
		return new_DB;
	}

	void PredicateAbstraction::guessCandidate(HornClauseDB &db)
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

	Expr PredicateAbstraction::relToCand(Expr fdecl)
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

	Expr PredicateAbstraction::fAppToCandApp(Expr fapp)
	{
	  Expr fdecl = bind::fname(fapp);
	  Expr cand = currentCandidates[fdecl];
	  return applyArgsToBvars(cand, fapp);
	}

	Expr PredicateAbstraction::applyArgsToBvars(Expr cand, Expr fapp)
	{
	  ExprMap bvar_map = getBvarsToArgsMap(fapp);
	  return replace(cand, bvar_map);
	}

	ExprMap PredicateAbstraction::getBvarsToArgsMap(Expr fapp)
	{
	  Expr fdecl = bind::fname(fapp);
	  Expr cand = currentCandidates[fdecl];

	  ExprMap bvar_map;
	  ExprVector bvars;
	  get_all_bvars(cand, std::back_inserter(bvars));

	  for(ExprVector::iterator it = bvars.begin(); it != bvars.end(); ++it)
	  {
		  unsigned bvar_id = bind::bvarId(*it);
		  Expr app_arg = fapp->arg(bvar_id + 1);// To improve
		  bvar_map.insert(std::pair<Expr,Expr>(*it, app_arg));
	  }
	  return bvar_map;
	}

	Expr PredicateAbstraction::extractTransitionRelation(HornRule r, HornClauseDB &db)
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

	struct IsPredApp : public std::unary_function<Expr, bool>
	{
		 HornClauseDB &m_db;
		 IsPredApp (HornClauseDB &db) : m_db (db) {}

		 bool operator() (Expr e)
		 {return bind::isFapp (e) && m_db.hasRelation (bind::fname(e));}
	};

	struct IsBVar : public std::unary_function<Expr, bool>
	{
		 IsBVar () {}
		 bool operator() (Expr e)
		 {return bind::isBVar (e);}
	};

	template<typename OutputIterator>
	void PredicateAbstraction::get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out)
	{filter (e, IsPredApp(db), out);}

	template<typename OutputIterator>
	void PredicateAbstraction::get_all_bvars (Expr e, OutputIterator out)
	{filter (e, IsBVar(), out);}

	void PredicateAbstraction::printInvars (Module &M)
	{
		for (auto &F : M) printInvars (F);
	}

	void PredicateAbstraction::printInvars (Function &F)
	{
		if (F.isDeclaration ()) return;

		HornifyModule &hm = getAnalysis<HornifyModule> ();
		outs () << "Function: " << F.getName () << "\n";

		// -- not used for now
		Expr summary = hm.summaryPredicate (F);

		ZFixedPoint<EZ3> fp = *m_fp;

		for (auto &BB : F)
		{
		  if (!hm.hasBbPredicate (BB)) continue;

		  Expr bbPred = hm.bbPredicate (BB);

		  outs () << *bind::fname (bbPred) << ":";
		  const ExprVector &live = hm.live (BB);
		  Expr invars = fp.getCoverDelta (bind::fapp (bbPred, live));

		  if (isOpX<AND> (invars))
		  {
			outs () << "\n\t";
			for (size_t i = 0; i < invars->arity (); ++i)
			  outs () << "\t" << *invars->arg (i) << "\n";
		  }
		  else
			outs () << " " << *invars << "\n";
		}
	}
}
