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

	bool PredicateAbstraction::runOnModule (Module &M)
	{
		HornifyModule &hm = getAnalysis<HornifyModule> ();

		PredicateAbstractionAnalysis pabs(hm);
		pabs.runAnalysis();

		return false;
	}

	void PredicateAbstraction::getAnalysisUsage (AnalysisUsage &AU) const
	{
		AU.addRequired<HornifyModule> ();
		AU.setPreservesAll();
	}

	void PredicateAbstractionAnalysis::runAnalysis()
	{
		//load the Horn clause database
		auto &db = m_hm.getHornClauseDB ();
		db.buildIndexes ();

		//guess candidates
		guessCandidate(db);

		HornDbModel oldModel;
		oldModel.setCurrentCandidates(currentCandidates);

		PredAbsHornModelConverter converter;

		//run main algorithm
		HornClauseDB new_db = generateAbstractDB(db, converter);

		//initialize spacer based on new DB
		m_fp.reset (new ZFixedPoint<EZ3> (m_hm.getZContext ()));
		ZFixedPoint<EZ3> &fp = *m_fp;
		ZParams<EZ3> params (m_hm.getZContext ());
		params.set (":engine", "spacer");
		// -- disable slicing so that we can use cover
		params.set (":xform.slice", false);
		params.set (":use_heavy_mev", true);
		params.set (":reset_obligation_queue", true);
		params.set (":pdr.flexible_trace", false);
		params.set (":xform.inline-linear", false);
		params.set (":xform.inline-eager", false);
		// -- disable utvpi. It is unstable.
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
		if (result) outs () << "sat";
		else if (!result)
		{
			outs() << "unsat\n";
			HornDbModel absModel;
			absModel.initModelFromFP(new_db, fp);
			converter.setNewToOldPredMap(newToOldPredMap);
			converter.setAbsDB(new_db);
			converter.convert(absModel, oldModel);
			outs() << "FINAL RESULT:\n";
			//Print invariants
			printInvars(db, oldModel);
		}
		else outs () << "unknown";
		outs () << "\n";
	}

	void HornDbModel::addDef(Expr fapp, Expr def)
	{
		if(isOpX<TRUE>(def) || isOpX<FALSE>(def))
		{
			relToDefMap.insert(std::pair<Expr, Expr>(bind::fname(fapp), def));
			return;
		}

		std::ostringstream oss;
		oss << bind::fname(bind::fname(fapp));
		//For AbsModel
		if(oss.str().find("_pabs") != -1)
		{
			ExprVector booleanVars;
			HornDbUtils::get_all_booleans(def, std::back_inserter(booleanVars));
			ExprMap boolVarsToBvarsMap;
			for(Expr boolvar : booleanVars)
			{
				for(int i=0; i<bind::domainSz(bind::fname(fapp)); i++)
				{
					Expr arg_i = fapp->arg(i+1);
					if(arg_i == boolvar)
					{
						Expr encoded_solution = bind::bvar(i, mk<BOOL_TY>(arg_i->efac()));
						outs() << "ENCODED SOLUTION: " << *encoded_solution << "\n";
						boolVarsToBvarsMap.insert(std::pair<Expr, Expr>(boolvar, encoded_solution));
					}
				}
			}
			def = replace(def, boolVarsToBvarsMap);
			relToDefMap.insert(std::pair<Expr, Expr>(bind::fname(fapp), def));
		}
		//For OrigModel
		else
		{
			ExprVector vars;
			HornDbUtils::get_all_integers(def, std::back_inserter(vars));
			ExprMap varIdMap;
			for(Expr var : vars)
			{
				int var_id = variant::variantNum(bind::fname(bind::fname(var)));
				Expr bvar = bind::intBVar(var_id, var->efac());
				varIdMap.insert(std::pair<Expr, Expr>(var, bvar));
			}
			Expr orig_def = replace(def, varIdMap);
			outs() << "ADD BVAR DEF: " << *orig_def << "\n";
			relToDefMap.insert(std::pair<Expr, Expr>(bind::fname(fapp), orig_def));
		}
	}

	Expr HornDbModel::getDef(Expr fapp)
	{
		std::ostringstream oss;
		oss << bind::fname(bind::fname(fapp));
		//AbsModel
		if(oss.str().find("_pabs") != -1)
		{
			Expr rel = bind::fname(fapp);
			Expr def = relToDefMap.find(rel)->second;
			ExprMap bvarToBoolVarMap;
			ExprVector bvars;
			HornDbUtils::get_all_bvars(def, std::back_inserter(bvars));
			for(Expr bvar : bvars)
			{
				int bvar_id = bind::bvarId(bvar);
				bvarToBoolVarMap.insert(std::pair<Expr, Expr>(bvar, fapp->arg(bvar_id+1)));
			}
			Expr def_app = replace(def, bvarToBoolVarMap);
			return def_app;
		}
		//OrigModel
		else
		{
			Expr rel = bind::fname(fapp);
			Expr def = relToDefMap.find(rel)->second;
			Expr def_app = HornDbUtils::applyArgsToBvars(def, fapp, currentCandidates);
			return def_app;
		}
	}

	void HornDbModel::initModelFromFP(HornClauseDB &db, ZFixedPoint<EZ3> &fp)
	{
		ExprVector all_preds_in_DB;
		for(HornRule r : db.getRules())
		{
			Expr pred = r.head();
			all_preds_in_DB.push_back(pred);
		}
		for(Expr pred : all_preds_in_DB)
		{
			outs() << "REL: " << *(bind::fname(pred)) << "\n";
			Expr solution = fp.getCoverDelta(pred);
			outs() << "SOLUTION: " << *solution << "\n";
			addDef(pred, solution);
		}
	}

	bool PredAbsHornModelConverter::convert (HornDbModel &in, HornDbModel &out)
	{
		for(std::map<Expr, ExprMap>::iterator it = getRelToBoolToTermMap().begin(); it!=getRelToBoolToTermMap().end(); ++it)
		{
			outs() << "REL: " << *(it->first) << "\n";
			outs() << "BOOL: " << *(it->second.begin()->first) << "\n";
			outs() << "TERM: " << *(it->second.begin()->second) << "\n";
		}
		for(Expr abs_rel : abs_db->getRelations())
		{
			outs() << "ABS REL: " << *abs_rel << "\n";
			Expr orig_rel = newToOldPredMap.find(abs_rel)->second;
			outs() << "ORIG REL: " << *orig_rel << "\n";

			ExprVector abs_arg_list;
			for(int i=0; i<bind::domainSz(abs_rel); i++)
			{
				Expr boolVar = bind::boolConst(variant::variant(i, mkTerm<std::string>("b", orig_rel->efac())));
				abs_arg_list.push_back(boolVar);
			}
			Expr abs_rel_app = bind::fapp(abs_rel, abs_arg_list);
			outs() << "ABS REL APP: " << *abs_rel_app << "\n";
			Expr abs_def_app = in.getDef(abs_rel_app);
			outs() << "ABS DEF APP: " << *abs_def_app << "\n";
			ExprMap boolVarToBvarMap;
			ExprVector bools;
			HornDbUtils::get_all_booleans(abs_def_app, std::back_inserter(bools));
			for(Expr boolvar: bools)
			{
				Expr bool_bvar = bind::boolBVar(variant::variantNum(bind::fname(bind::fname(boolvar))), boolvar->efac());
				boolVarToBvarMap.insert(std::pair<Expr,Expr>(boolvar, bool_bvar));
			}
			Expr abs_def = replace(abs_def_app, boolVarToBvarMap);

			outs() << "ABS DEF: " << *abs_def << "\n";
			Expr orig_def;
			if(isOpX<TRUE>(abs_def) || isOpX<FALSE>(abs_def))
			{
				orig_def = abs_def;
			}
			else
			{
				orig_def = (getRelToBoolToTermMap().find(orig_rel)->second).find(abs_def)->second;
			}
			outs() << "ORIG DEF: " << *orig_def << "\n";

			ExprVector orig_fapp_args;
			for(int i=0; i<bind::domainSz(orig_rel); i++)
			{
				Expr var = bind::intConst(variant::variant(i, mkTerm<std::string> ("V", orig_rel->efac ())));
				orig_fapp_args.push_back(var);
			}
			Expr orig_fapp = bind::fapp(orig_rel, orig_fapp_args);
			outs() << "ORIG FAPP: " << *orig_fapp << "\n";
			ExprVector bvars;
			HornDbUtils::get_all_bvars(orig_def, std::back_inserter(bvars));
			ExprMap bvarIdMap;
			for(Expr bvar : bvars)
			{
				int bvar_id = bind::bvarId(bvar);
				Expr var = bind::intConst(variant::variant(bvar_id, mkTerm<std::string> ("V", bvar->efac ())));
				bvarIdMap.insert(std::pair<Expr, Expr>(bvar, var));
			}
			Expr orig_def_app = replace(orig_def, bvarIdMap);
			outs() << "ORIG DEF APP: " << *orig_def_app << "\n";
			out.addDef(orig_fapp, orig_def_app);
			//out.getRelToSolutionMap().insert(std::pair<Expr, Expr>(orig_rel, orig_def));
//			for(ExprMap::iterator it = out.getRelToSolutionMap().begin(); it!=out.getRelToSolutionMap().end(); ++it)
//			{
//				outs() << "ORIG REL: " << *(it->first) << ", ORIG DEF: " << *(it->second) << "\n";
//			}
		}
		return true;
	}

	HornClauseDB PredicateAbstractionAnalysis::generateAbstractDB(HornClauseDB &db, PredAbsHornModelConverter &converter)
	{
		HornClauseDB new_DB(db.getExprFactory ());

		generateAbstractRelations(db, new_DB);

		generateAbstractRules(db, new_DB, converter);

		generateAbstractQueries(db, new_DB);

		LOG("pabs-debug", outs() << "NEW DB: \n";);
		LOG("pabs-debug", outs() << new_DB << "\n";);

		return new_DB;
	}

	void PredicateAbstractionAnalysis::generateAbstractRelations(HornClauseDB &db, HornClauseDB &new_DB)
	{
		//For each relation, generate its abstract version
		for(Expr rel : db.getRelations())
		{
			LOG("pabs-debug", outs() << "OLD REL: " << *rel << "\n";);
			ExprVector new_args;
			//Push fdecl name
			Expr old_fdecl_name = bind::fname(rel);
			std::ostringstream oss;
			oss << old_fdecl_name << "_pabs";
			new_args.push_back(old_fdecl_name);
			//Push boolean types
			ExprVector term_vec = currentCandidates.find(rel)->second;
			if(term_vec.size() > 1 || term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0]))
			{
				for(int i=0; i<term_vec.size(); i++)
				{
					new_args.push_back(mk<BOOL_TY>(rel->efac()));
				}
			}
			else // the candidate term is just 'true' or 'false'
			{
				for (int i=1; i<=bind::domainSz(rel); i++ )
				{
					new_args.push_back(bind::domainTy(rel, i));
				}
			}
			//Push return type
			new_args.push_back(bind::rangeTy(rel));
			Expr new_rel = mknary<FDECL>(new_args);

			//new pred name
			Expr new_fdecl_name = mkTerm<std::string>(oss.str(), new_rel->efac());
			new_rel = bind::rename(new_rel, new_fdecl_name);

			LOG("pabs-debug", outs() << "NEW REL: " << *new_rel << "\n";);
			new_DB.registerRelation(new_rel);

			oldToNewPredMap.insert(std::pair<Expr, Expr>(rel, new_rel));
			newToOldPredMap.insert(std::pair<Expr, Expr>(new_rel, rel));
		}
	}

	void PredicateAbstractionAnalysis::generateAbstractRules(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter)
	{
		for(HornClauseDB::RuleVector::iterator it = db.getRules().begin(); it != db.getRules().end(); ++it)
		{
			HornRule r = *it;
			LOG("pabs-debug", outs() << "OLD RULE HEAD: " << *(r.head()) << "\n";);
			LOG("pabs-debug", outs() << "OLD RULE BODY: " << *(r.body()) << "\n";);

			//old rule variables
			ExprVector rule_vars;
			rule_vars.insert(rule_vars.end(), r.vars().begin(), r.vars().end());

			//Map for counting occurrence time for each relation in per rule
			std::map<Expr, int> relOccurrenceTimesMap;

			ExprVector pred_vector;
			HornDbUtils::get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
			pred_vector.push_back(r.head());

			//Deal with the rules that have no predicates
			if(!HornDbUtils::hasBvarInRule(r, db, currentCandidates))
			{
				ExprMap replaceMap;
				for(Expr pred : pred_vector)
				{
					Expr new_fdecl = oldToNewPredMap.find(bind::fname(pred))->second;
					Expr new_pred = bind::reapp(pred, new_fdecl);
					replaceMap.insert(std::pair<Expr, Expr>(pred, new_pred));
				}
				Expr new_head = replace(r.head(), replaceMap);
				Expr new_body = replace(r.body(), replaceMap);
				HornRule new_rule(r.vars(), new_head, new_body);
				new_DB.addRule(new_rule);
				continue;
			}

			//initialize the occurrence count map
			for(ExprVector::iterator it = pred_vector.begin(); it!= pred_vector.end(); ++it)
			{
				relOccurrenceTimesMap.insert(std::pair<Expr, int>(bind::fname(*it), 0));
			}

			//construct new body
			ExprVector new_body_exprs;

			//For each predicate in the body, construct new version of predicate.
			Expr rule_body = r.body();
			ExprVector body_pred_apps;
			HornDbUtils::get_all_pred_apps(rule_body, db, std::back_inserter(body_pred_apps));
			for(ExprVector::iterator it = body_pred_apps.begin(); it != body_pred_apps.end(); ++it)
			{
				Expr rule_body_pred = *it;
				Expr new_rule_body_rel = oldToNewPredMap.find(bind::fname(rule_body_pred))->second;

				int pred_order = relOccurrenceTimesMap.find(bind::fname(rule_body_pred))->second;
				relOccurrenceTimesMap[bind::fname(rule_body_pred)] += 1;

				ExprVector new_rule_body_args;
				//Push boolean variables into arguments of new predicate

				for(int i=0; i<bind::domainSz(new_rule_body_rel); i++)
				{
					Expr var_tag = variant::variant(pred_order, variant::variant(i, variant::tag(bind::fname(new_rule_body_rel), mkTerm<std::string> ("p", new_rule_body_rel->efac ())))); //noprime
					Expr boolVar = bind::boolConst(var_tag);
					rule_vars.push_back(boolVar);
					new_rule_body_args.push_back(boolVar);
				}

				Expr new_rule_body_pred = bind::fapp(new_rule_body_rel, new_rule_body_args);
				new_body_exprs.push_back(new_rule_body_pred);

				//for each predicate in the body, create iff
				int index = 0;
				//for converter
				ExprMap boolToTermMap;
				for(Expr term : currentCandidates.find(bind::fname(*it))->second)
				{
					Expr term_app = HornDbUtils::applyArgsToBvars(term, *it, currentCandidates);
					Expr equal_expr = mk<IFF>(new_rule_body_pred->arg(index + 1), term_app);
					//converter
					boolToTermMap.insert(std::pair<Expr, Expr>(bind::bvar(index, mk<BOOL_TY>(term_app->efac())), term));

					new_body_exprs.push_back(equal_expr);
					index ++;
				}
				converter.getRelToBoolToTermMap().insert(std::pair<Expr, ExprMap>(bind::fname(*it), boolToTermMap));
			}

			Expr rule_head = r.head();

			//construct new rule head.
			Expr new_rule_head_rel = oldToNewPredMap.find(bind::fname(rule_head))->second;

			ExprVector new_rule_head_args;
			int pred_order = relOccurrenceTimesMap.find(bind::fname(rule_head))->second;
			relOccurrenceTimesMap[bind::fname(rule_head)] += 1;
			for(int i=0; i<bind::domainSz(new_rule_head_rel); i++)
			{
				Expr var_tag = variant::variant(pred_order, variant::variant(i, variant::tag(bind::fname(new_rule_head_rel), mkTerm<std::string> ("p", new_rule_head_rel->efac ())))); //prime
				Expr boolVar = bind::boolConst(var_tag);
				rule_vars.push_back(boolVar);
				new_rule_head_args.push_back(boolVar);
			}

			Expr new_rule_head = bind::fapp(new_rule_head_rel, new_rule_head_args);
			outs() << "NEW RULE HEAD: " << *new_rule_head << "\n";


			if(bind::domainSz(bind::fname(rule_head)) != 0)
			{
				//construct head equality expr, put in new body
				int index = 0;
				//for converter
				ExprMap boolToTermMap;
				for(Expr term : currentCandidates.find(bind::fname(rule_head))->second)
				{
					Expr term_app = HornDbUtils::applyArgsToBvars(term, rule_head, currentCandidates);
					Expr equal_expr = mk<IFF>(new_rule_head->arg(index + 1), term_app);
					//converter
					boolToTermMap.insert(std::pair<Expr, Expr>(bind::bvar(index, mk<BOOL_TY>(term_app->efac())), term));

					new_body_exprs.push_back(equal_expr);
					index ++;
				}
				converter.getRelToBoolToTermMap().insert(std::pair<Expr, ExprMap>(bind::fname(rule_head), boolToTermMap));
			}

			//Extract the constraints
			Expr constraints = HornDbUtils::extractTransitionRelation(r, db);
			new_body_exprs.push_back(constraints);

			//Construct new body
			Expr new_rule_body = mknary<AND>(new_body_exprs.begin(), new_body_exprs.end());
			outs() << "NEW RULE BODY :" << *new_rule_body << "\n";

			HornRule new_rule(rule_vars, new_rule_head, new_rule_body);
			new_DB.addRule(new_rule);
		}
	}

	void PredicateAbstractionAnalysis::generateAbstractQueries(HornClauseDB &db, HornClauseDB &new_DB)
	{
		for(auto old_query : db.getQueries())
		{
			Expr old_fdecl = bind::fname(old_query);
			Expr new_fdecl = oldToNewPredMap.find(old_fdecl)->second;
			ExprVector old_args;
			Expr new_query = bind::fapp(new_fdecl, old_args);
			outs() << "NEW QUERY: " << *new_query << "\n";
			new_DB.addQuery(new_query);
		}
	}

	void PredicateAbstractionAnalysis::guessCandidate(HornClauseDB &db)
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

	ExprVector PredicateAbstractionAnalysis::relToCand(Expr fdecl)
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

			Expr one = mkTerm<mpz_class> (1, fdecl->efac());//
			bins.push_back(mk<GEQ>(bvars[0], one));//
		}
		// if there are more than two bvars, make an lt expr
		else if(bvar_count == 2)
		{
			Expr lt1 = mk<LT>(bvars[0], bvars[1]);
			Expr lt2 = mk<LT>(bvars[1], bvars[0]);
			bins.push_back(lt1);
			bins.push_back(lt2);

			//
			Expr one = mkTerm<mpz_class> (1, fdecl->efac());
			Expr geq1 = mk<GEQ>(bvars[0], one);
			Expr geq2 = mk<GEQ>(bvars[1], one);
			bins.push_back(geq1);
			bins.push_back(geq2);
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

	void PredicateAbstractionAnalysis::printInvars(HornClauseDB &db, HornDbModel &origModel)
	{
		ExprMap relToAppMap;
		for(HornRule r : db.getRules())
		{
			Expr pred = r.head();
			relToAppMap.insert(std::pair<Expr, Expr>(bind::fname(pred), pred));
		}
		for(ExprMap::iterator it = relToAppMap.begin(); it!=relToAppMap.end(); ++it)
		{
			Expr pred = it->second;
			Expr def = origModel.getDef(pred);
			outs() << *bind::fname(bind::fname(pred)) << ": " << *def << "\n";
		}
	}

	Expr HornDbUtils::applyArgsToBvars(Expr cand, Expr fapp, std::map<Expr, ExprVector> currentCandidates)
	{
	  ExprMap bvar_map = getBvarsToArgsMap(fapp, currentCandidates);
	  return replace(cand, bvar_map);
	}

	ExprMap HornDbUtils::getBvarsToArgsMap(Expr fapp, std::map<Expr, ExprVector> currentCandidates)
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
	  HornDbUtils::get_all_bvars(cand, std::back_inserter(bvars));

	  for(ExprVector::iterator it = bvars.begin(); it != bvars.end(); ++it)
	  {
		  unsigned bvar_id = bind::bvarId(*it);
		  Expr app_arg = fapp->arg(bvar_id + 1);// To improve
		  bvar_map.insert(std::pair<Expr,Expr>(*it, app_arg));
	  }
	  return bvar_map;
	}

	Expr HornDbUtils::extractTransitionRelation(HornRule r, HornClauseDB &db)
	{
	  Expr ruleBody = r.body();
	  ExprMap body_map;
	  ExprVector body_pred_apps;
	  HornDbUtils::get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));

	  for(ExprVector::iterator itr = body_pred_apps.begin(); itr != body_pred_apps.end(); ++itr)
	  {
		  body_map.insert(std::pair<Expr, Expr>(*itr, mk<TRUE>((*itr)->efac())));
	  }

	  Expr body_constraints = replace(ruleBody, body_map);
	  return body_constraints;
	}

	bool HornDbUtils::hasBvarInRule(HornRule r, HornClauseDB &db, std::map<Expr, ExprVector> currentCandidates)
	{
		ExprVector pred_vector;
		HornDbUtils::get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
		pred_vector.push_back(r.head());

		for (Expr pred : pred_vector)
		{
			ExprVector term_vec = currentCandidates.find(bind::fname(pred))->second;
			if(term_vec.size() > 1 || term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0]))
			{
				return true;
			}
		}
		return false;
	}
}
