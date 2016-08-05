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

    std::map<Expr, Expr> PredicateAbstraction::oldToNewPredMap;
    std::map<Expr, ExprVector> PredicateAbstraction::currentCandidates;

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
		outs() << "Vars:\n";
		for(Expr e : db.getVars())
		{
			outs() << *e << "\n";
		}

		HornClauseDB new_DB(db.getExprFactory ());

		for(Expr rel : db.getRelations())
		{
			outs() << "OLD PRED: " << *rel << "\n";
			ExprVector new_args;
			//Push fdecl name
			new_args.push_back(bind::fname(rel));
			//Push boolean types
			ExprVector term_vec = currentCandidates.find(rel)->second;
			if(term_vec.size() > 1 || term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0]))
			{
				for(int i=0; i<term_vec.size(); i++)
				{
					new_args.push_back(mk<BOOL_TY>(rel->efac()));
				}
			}
			else
			{
				for (int i=1; i<=bind::domainSz(rel); i++ )
				{
					new_args.push_back(bind::domainTy(rel, i));
				}
			}
			//Push return type
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

			ExprVector rule_vars;
			rule_vars.insert(rule_vars.end(), r.vars().begin(), r.vars().end());

			//Map from predicate apps to bool vars
			std::map<Expr, Expr> predAppToBoolVarMap;

			//Count occurrence time for each relation in per rule
			std::map<Expr, int> relOccurrenceTimesMap;

			ExprVector pred_vector;
			get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
			pred_vector.push_back(r.head());

			bool isSkip = true;
			for (Expr pred : pred_vector)
			{
				ExprVector term_vec = currentCandidates.find(bind::fname(pred))->second;
				if(term_vec.size() > 1 || term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0]))
				{
					isSkip = false;
				}
			}
			if(isSkip)
			{
				new_DB.addRule(r);
				continue;
			}

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
			int head_rel_occur_time = relOccurrenceTimesMap.find(bind::fname(rule_head))->second;
			if(head_rel_occur_time == 2) //Both head and body
			{
				for(int i=0; i<bind::domainSz(new_rule_head_rel); i++)
				{
					Expr boolVar = variant::variant(1, variant::variant(i, variant::tag(bind::fname(new_rule_head_rel), mkTerm<std::string> ("p", new_rule_head_rel->efac ())))); //prime
					rule_vars.push_back(boolVar);
					new_rule_head_args.push_back(boolVar);
				}
			}
			else if(head_rel_occur_time == 1) //only in head
			{
				for(int i=0; i<bind::domainSz(new_rule_head_rel); i++)
				{
					Expr boolVar = variant::variant(0, variant::variant(i, variant::tag(bind::fname(new_rule_head_rel), mkTerm<std::string> ("p", new_rule_head_rel->efac ())))); //noprime
					rule_vars.push_back(boolVar);
					new_rule_head_args.push_back(boolVar);
				}
			}
			else
			{
				errs() << "OCCUR TIMES WRONG!\n";
				assert(false);
			}

			Expr new_rule_head = bind::fapp(new_rule_head_rel, new_rule_head_args);
			outs() << "NEW RULE HEAD: " << *new_rule_head << "\n";

			//construct new body
			ExprVector new_body_exprs;

			if(bind::domainSz(bind::fname(rule_head)) != 0)
			{
				//construct head equality expr
				int index = 0;
				for(Expr term : currentCandidates.find(bind::fname(rule_head))->second)
				{
					Expr term_app = applyArgsToBvars(term, rule_head);
					Expr equal_expr = mk<IFF>(new_rule_head->arg(index + 1), term_app);

					new_body_exprs.push_back(equal_expr);
					index ++;
				}
				outs() << "RULE HEAD IFF: \n";
				for (Expr e : new_body_exprs)
				{
					outs() << *e << "\n";
				}
			}

			//For each predicate in the body, construct new version of predicate.
			Expr rule_body = r.body();
			ExprVector body_pred_apps;
			get_all_pred_apps(rule_body, db, std::back_inserter(body_pred_apps));
			for(ExprVector::iterator it = body_pred_apps.begin(); it != body_pred_apps.end(); ++it)
			{
				Expr rule_body_pred = *it;
				assert(oldToNewPredMap.find(bind::fname(rule_body_pred)) != oldToNewPredMap.end());
				Expr new_rule_body_rel = oldToNewPredMap.find(bind::fname(rule_body_pred))->second;

				ExprVector new_rule_body_args;
				//Push boolean variables into arguments of new predicate

				for(int i=0; i<bind::domainSz(new_rule_body_rel); i++)
				{
					Expr boolVar = variant::variant(0, variant::variant(i, variant::tag(bind::fname(new_rule_body_rel), mkTerm<std::string> ("p", new_rule_body_rel->efac ())))); //noprime
					rule_vars.push_back(boolVar);
					new_rule_body_args.push_back(boolVar);
				}

				Expr new_rule_body_pred = bind::fapp(new_rule_body_rel, new_rule_body_args);
				new_body_exprs.push_back(new_rule_body_pred);

				//for each predicate in the body, create iff
				int index = 0;
				for(Expr term : currentCandidates.find(bind::fname(*it))->second)
				{
					Expr term_app = applyArgsToBvars(term, *it);
					Expr equal_expr = mk<IFF>(new_rule_body_pred->arg(index + 1), term_app);

					new_body_exprs.push_back(equal_expr);
					index ++;
				}
			}

			//Extract the constraints
			Expr constraints = extractTransitionRelation(r, db);
			new_body_exprs.push_back(constraints);
			//Construct new body
			Expr new_rule_body = mknary<AND>(new_body_exprs.begin(), new_body_exprs.end());
			outs() << "NEW RULE BODY :" << *new_rule_body << "\n";
			HornRule new_rule(rule_vars, new_rule_head, new_rule_body);
			new_DB.addRule(new_rule);
		}
//		 errs () << "QUERIES 2\n";
//		        for (auto q: db.getQueries ())
//		        	errs () << *q << "\n";

		for(auto old_query : db.getQueries())
		{
			Expr new_query = old_query;
			outs() << "NEW QUERY: " << *new_query << "\n";
			new_DB.addQuery(new_query);
		}

		outs() << "NEW DB: \n";
		outs() << new_DB << "\n";
		outs() << "Vars:\n";
		for(Expr e : new_DB.getVars())
		{
			outs() << *e << "\n";
		}
		return new_DB;
	}

	void PredicateAbstraction::guessCandidate(HornClauseDB &db)
	{
	  for(Expr rel : db.getRelations())
	  {
		  if(bind::isFdecl(rel))
		  {
			  ExprVector terms = relToCand(rel);
			  currentCandidates.insert(std::pair<Expr, ExprVector>(rel, terms));
		  }
	  }
	}

	ExprVector PredicateAbstraction::relToCand(Expr fdecl)
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
			bins.push_back(mk<TRUE>(fdecl->efac()));
		}
		// if there is only one bvar, create a int constant and make an lt expr
		else if(bvar_count == 1)
		{
			Expr zero = mkTerm<mpz_class> (0, fdecl->efac());
			bins.push_back(mk<LT>(bvars[0], zero));
		}
		// if there are more than two bvars, make an lt expr
		else if(bvar_count == 2)
		{
			Expr lt1 = mk<LT>(bvars[0], bvars[1]);
			Expr lt2 = mk<LT>(bvars[1], bvars[0]);
			bins.push_back(lt1);
			bins.push_back(lt2);
		}
		else // bvar_count > 2
		{
			for(int j=0; j<bvars.size()-1; j++)
			{
				Expr lt = mk<LT>(bvars[j], bvars[j+1]);
				bins.push_back(lt);
			}
		}

		return bins;
	}

	Expr PredicateAbstraction::applyArgsToBvars(Expr cand, Expr fapp)
	{
	  ExprMap bvar_map = getBvarsToArgsMap(fapp);
	  return replace(cand, bvar_map);
	}

	ExprMap PredicateAbstraction::getBvarsToArgsMap(Expr fapp)
	{
	  Expr fdecl = bind::fname(fapp);
	  ExprVector terms = currentCandidates[fdecl];
	  Expr cand;
	  if(terms.size() == 1)
	  {
		  cand = currentCandidates[fdecl][0];
	  }
	  else if(terms.size() > 1)
	  {
		  cand = mknary<AND>(terms.begin(), terms.end());
	  }
	  else
	  {
		  errs() << "terms size wrong!\n";
		  assert(false);
	  }

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
