#include "seahorn/PredicateAbstraction.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/HornClauseDB.hh"
#include "seahorn/GuessCandidates.hh"

#include "seahorn/HornDbModel.hh"
#include "seahorn/HornModelConverter.hh"

#include "llvm/IR/Function.h"
#include "llvm/Support/CommandLine.h"

#include "seahorn/Expr/Expr.hh"
#include "seahorn/Expr/Smt/EZ3.hh"
#include <vector>
#include <boost/logic/tribool.hpp>
#include "seahorn/HornClauseDBWto.hh"
#include <algorithm>

#include "seahorn/Support/Stats.hh"

using namespace llvm;

static llvm::cl::opt<std::string>
UserCandidatesFile ("pa-candidates-file",
		    llvm::cl::desc ("Read candidates from a file"),
		    cl::init ("preds_temp"),
		    cl::Hidden);

namespace seahorn
{
  char PredicateAbstraction::ID = 0;

  bool PredicateAbstraction::runOnModule (Module &M)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    PredicateAbstractionAnalysis pabs(hm);
    Stats::resume ("Pabs solve");
    
    //load the Horn clause database
    auto &db = hm.getHornClauseDB ();
    if (db.hasQuery ()) {
      bool all_true = true;
      bool any_false= false;

      // check for trivial queries
      for (auto q: db.getQueries ()) {
	if (!isOpX<TRUE>(q)) all_true = false;
	if (isOpX<FALSE>(q)) any_false = true;
      }

      if (all_true) {
	//outs () << "sat";
      } else if (any_false) {
	//outs () << "unsat";
      } else {
	db.buildIndexes ();
	
	//guess candidates
	pabs.guessCandidate(db);
	
	HornDbModel oldModel;
	
	PredAbsHornModelConverter converter;
	
	//run main algorithm
	HornClauseDB new_db(db.getExprFactory());
	pabs.generateAbstractDB(db, new_db, converter);
	
	//initialize spacer based on new DB
	m_fp.reset (new ZFixedPoint<EZ3> (hm.getZContext ()));
	ZFixedPoint<EZ3> &fp = *m_fp;
	ZParams<EZ3> params (hm.getZContext ());
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
	// -- disable propagate_variable_equivalences in tail_simplifier
	params.set (":xform.tail_simplifier_pve", false);
	params.set (":xform.subsumption_checker", true);
	//		params.set (":order_children", true);
	//		params.set (":pdr.max_num_contexts", "500");
	fp.set (params);
	new_db.loadZFixedPoint (fp, false);
	boost::tribool result = fp.query ();
	
	LOG("pabs-smt2", outs() << "SMT2: " << fp << "\n";);
	
	if (result) {
	  outs () << "sat";
	} else if (!result) {
	  outs() << "unsat\n";
	  HornDbModel absModel;
	  initDBModelFromFP(absModel, new_db, fp);
	  
	  converter.convert(absModel, oldModel);
	  LOG("pabs-debug", outs() << "FINAL RESULT:\n";);
	  //Print invariants
	  printInvars(M, oldModel);
	} else {
	  outs () << "unknown";
	}
      }
    } else {
      // no query so trivially unsat
      //outs () << "unsat";      
    }
    outs () << "\n";
    Stats::stop("Pabs solve");
    return false;
  }
  
  void PredicateAbstraction::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.addRequired<HornifyModule> ();
    AU.setPreservesAll();
  }

  void PredicateAbstraction::printInvars (Module &M, HornDbModel &origModel)
  {
    for (auto &F : M) printInvars (F, origModel);
  }

  void PredicateAbstraction::printInvars(Function &F, HornDbModel &origModel)
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
      //Expr invars = fp.getCoverDelta (bind::fapp (bbPred, live));
      Expr invars = origModel.getDef(bind::fapp(bbPred, live));

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

  void PredicateAbstractionAnalysis::generateAbstractDB(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter)
  {
    generateAbstractRelations(db, new_DB, converter);

    generateAbstractRules(db, new_DB, converter);

    generateAbstractQueries(db, new_DB);

    LOG("pabs-debug", outs() << "NEW DB: \n";);
    LOG("pabs-debug", outs() << new_DB << "\n";);

    converter.setAbsDB(new_DB); //set converter
  }

  void PredicateAbstractionAnalysis::generateAbstractRelations(HornClauseDB &db, HornClauseDB &new_DB, PredAbsHornModelConverter &converter)
  {
    //For each relation, generate its abstract version
    for(Expr rel : db.getRelations())
    {
      LOG("pabs-debug", outs() << "OLD REL: " << *rel << "\n";);
      ExprVector new_args;

      Expr old_fdecl_name = bind::fname(rel);
      //new pred name
      std::string postfix = "pabs";
      Expr new_fdecl_name = variant::tag(old_fdecl_name, postfix);
      new_args.push_back(new_fdecl_name);
      //Push boolean types
      ExprVector term_vec = m_currentCandidates.find(rel)->second;
      if(term_vec.size() > 1 || (term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0])))
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

      LOG("pabs-debug", outs() << "NEW REL: " << *new_rel << "\n";);
      new_DB.registerRelation(new_rel);

      m_oldToNewPredMap.insert(std::make_pair(rel, new_rel));
      m_newToOldPredMap.insert(std::make_pair(new_rel, rel));
    }
    converter.setNewToOldPredMap(m_newToOldPredMap); //set converter
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
      get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
      pred_vector.push_back(r.head());

      //Deal with the rules that have no predicates
      if(!hasBvarInRule(r, db, m_currentCandidates))
      {
        ExprMap replaceMap;
        for(Expr pred : pred_vector)
        {
          Expr new_fdecl = m_oldToNewPredMap.find(bind::fname(pred))->second;
          Expr new_pred = bind::reapp(pred, new_fdecl);
          replaceMap.insert(std::make_pair(pred, new_pred));
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
        relOccurrenceTimesMap.insert(std::make_pair(bind::fname(*it), 0));
      }

      //construct new body
      ExprVector new_body_exprs;

      //For each predicate in the body, construct new version of predicate.
      Expr rule_body = r.body();
      ExprVector body_pred_apps;
      get_all_pred_apps(rule_body, db, std::back_inserter(body_pred_apps));
      for(ExprVector::iterator it = body_pred_apps.begin(); it != body_pred_apps.end(); ++it)
      {
        Expr rule_body_pred = *it;
        Expr new_rule_body_rel = m_oldToNewPredMap.find(bind::fname(rule_body_pred))->second;

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
        if(bind::domainSz(bind::fname(new_rule_body_pred)) == 0)
        {
          continue;
        }
        int index = 0;
        //for converter
        ExprMap boolToTermMap;
        for(Expr term : m_currentCandidates.find(bind::fname(*it))->second)
        {
          Expr term_app = applyArgsToBvars(term, *it, m_currentCandidates);
          Expr equal_expr = mk<IFF>(new_rule_body_pred->arg(index + 1), term_app);
          //converter
          boolToTermMap.insert(std::make_pair(bind::bvar(index, mk<BOOL_TY>(term_app->efac())), term));

          new_body_exprs.push_back(equal_expr);
          index ++;
        }
        converter.addRelToBoolToTerm(bind::fname(*it), boolToTermMap);
        //converter.getRelToBoolToTermMap().insert(std::pair<Expr, ExprMap>(bind::fname(*it), boolToTermMap));
      }

      Expr rule_head = r.head();

      //construct new rule head.
      Expr new_rule_head_rel = m_oldToNewPredMap.find(bind::fname(rule_head))->second;

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
      LOG("pabs-debug", outs() << "NEW RULE HEAD: " << *new_rule_head << "\n";);


      if(bind::domainSz(bind::fname(rule_head)) != 0)
      {
        //construct head equality expr, put in new body
        int index = 0;
        //for converter
        ExprMap boolToTermMap;
        for(Expr term : m_currentCandidates.find(bind::fname(rule_head))->second)
        {
          Expr term_app = applyArgsToBvars(term, rule_head, m_currentCandidates);
          Expr equal_expr = mk<IFF>(new_rule_head->arg(index + 1), term_app);
          //converter
          boolToTermMap.insert(std::make_pair(bind::bvar(index, mk<BOOL_TY>(term_app->efac())), term));

          new_body_exprs.push_back(equal_expr);
          index ++;
        }
        converter.addRelToBoolToTerm(bind::fname(rule_head), boolToTermMap);
        //converter.getRelToBoolToTermMap().insert(std::pair<Expr, ExprMap>(bind::fname(rule_head), boolToTermMap));
      }

      //Extract the constraints
      Expr constraints = extractTransitionRelation(r, db);
      new_body_exprs.push_back(constraints);

      //Construct new body
      Expr new_rule_body = mknary<AND>(new_body_exprs.begin(), new_body_exprs.end());
      LOG("pabs-debug", outs() << "NEW RULE BODY :" << *new_rule_body << "\n";);

      HornRule new_rule(rule_vars, new_rule_head, new_rule_body);
      new_DB.addRule(new_rule);
    }
  }

  void PredicateAbstractionAnalysis::generateAbstractQueries(HornClauseDB &db, HornClauseDB &new_DB)
  {
    for(auto old_query : db.getQueries())
    {
      Expr old_fdecl = bind::fname(old_query);
      Expr new_fdecl = m_oldToNewPredMap.find(old_fdecl)->second;
      ExprVector old_args;
      Expr new_query = bind::fapp(new_fdecl, old_args);
      new_DB.addQuery(new_query);
    }
  }

  void PredicateAbstractionAnalysis::guessCandidate(HornClauseDB &db)
  {
    for(Expr rel : db.getRelations())
    {
      if(bind::isFdecl(rel))
      {
        //ExprVector terms = relToCand(rel);
        ExprVector terms = applyTemplatesFromExperimentFile(rel, UserCandidatesFile);
        m_currentCandidates.insert(std::make_pair(rel, terms));
      }
    }
  }

  Expr PredicateAbstractionAnalysis::applyArgsToBvars(Expr cand, Expr fapp, std::map<Expr, ExprVector> currentCandidates)
  {
    ExprMap bvar_map = getBvarsToArgsMap(fapp, currentCandidates);
    return replace(cand, bvar_map);
  }

  ExprMap PredicateAbstractionAnalysis::getBvarsToArgsMap(Expr fapp, std::map<Expr, ExprVector> currentCandidates)
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
      bvar_map.insert(std::make_pair(*it, app_arg));
    }
    return bvar_map;
  }

  bool PredAbsHornModelConverter::convert (HornDbModel &in, HornDbModel &out)
  {
    for(Expr abs_rel : m_abs_db->getRelations())
    {
      LOG("pabs-debug", outs() << "ABS REL: " << *abs_rel << "\n";);

      Expr orig_rel = m_newToOldPredMap.find(abs_rel)->second;
      LOG("pabs-debug", outs() << "ORIG REL: " << *orig_rel << "\n";);

      ExprVector abs_arg_list;
      for(int i=0; i<bind::domainSz(abs_rel); i++)
      {
        Expr boolVar = bind::boolConst(variant::variant(i, mkTerm<std::string>("b", orig_rel->efac())));
        abs_arg_list.push_back(boolVar);
      }
      Expr abs_rel_app = bind::fapp(abs_rel, abs_arg_list);
      LOG("pabs-debug", outs() << "ABS REL APP: " << *abs_rel_app << "\n";);

      Expr abs_def_app = in.getDef(abs_rel_app);
      LOG("pabs-debug", outs() << "ABS DEF APP: " << *abs_def_app << "\n";);

      ExprMap boolVarToBvarMap;
      ExprVector bools;
      get_all_booleans(abs_def_app, std::back_inserter(bools));
      for(Expr boolvar: bools)
      {
        Expr bool_bvar = bind::boolBVar(variant::variantNum(bind::fname(bind::fname(boolvar))), boolvar->efac());
        boolVarToBvarMap.insert(std::make_pair(boolvar, bool_bvar));
      }
      Expr abs_def = replace(abs_def_app, boolVarToBvarMap);
      LOG("pabs-debug", outs() << "ABS DEF: " << *abs_def << "\n";);

      Expr orig_def;
      if(isOpX<TRUE>(abs_def) || isOpX<FALSE>(abs_def))
      {
        orig_def = abs_def;
      }
      else
      {
        ExprMap abs_bvar_to_term_map;
        ExprVector abs_bvars;
        get_all_bvars(abs_def, std::back_inserter(abs_bvars));
        for(Expr abs_bvar : abs_bvars)
        {
          Expr term = (getRelToBoolToTermMap().find(orig_rel)->second).find(abs_bvar)->second;
          abs_bvar_to_term_map.insert(std::make_pair(abs_bvar, term));
        }
        orig_def = replace(abs_def, abs_bvar_to_term_map);
      }
      LOG("pabs-debug", outs() << "ORIG DEF: " << *orig_def << "\n";);

      ExprVector orig_fapp_args;
      for(int i=0; i<bind::domainSz(orig_rel); i++)
      {
        Expr arg_i_type = bind::domainTy(orig_rel, i);
        Expr var = bind::fapp(bind::constDecl(variant::variant(i, mkTerm<std::string> ("V", orig_rel->efac ())), arg_i_type));
        orig_fapp_args.push_back(var);
      }
      Expr orig_fapp = bind::fapp(orig_rel, orig_fapp_args);
      LOG("pabs-debug", outs() << "ORIG FAPP: " << *orig_fapp << "\n";);

      ExprVector bvars;
      get_all_bvars(orig_def, std::back_inserter(bvars));
      ExprMap bvarIdMap;
      for(Expr bvar : bvars)
      {
        int bvar_id = bind::bvarId(bvar);
        Expr bvar_type = bind::typeOf(bvar);
        Expr var = bind::fapp(bind::constDecl(variant::variant(bvar_id, mkTerm<std::string> ("V", bvar->efac ())), bvar_type));
        bvarIdMap.insert(std::make_pair(bvar, var));
      }
      Expr orig_def_app = replace(orig_def, bvarIdMap);
      LOG("pabs-debug", outs() << "ORIG DEF APP: " << *orig_def_app << "\n";);
      out.addDef(orig_fapp, orig_def_app);
    }
    return true;
  }
}
