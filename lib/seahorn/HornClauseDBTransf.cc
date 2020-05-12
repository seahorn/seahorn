#include "seahorn/HornClauseDBTransf.hh"
#include "seahorn/Expr/Expr.hh"

#include "seahorn/FiniteMapTransf.hh"

namespace seahorn {
using namespace expr;

// Return a new Horn rule whose head only has variables
HornRule replaceNonVarsInHead(const HornRule &rule) {
  Expr h = rule.head();
  assert(bind::isFapp(h));
  ExprFactory &efac = h->efac();

  auto it = ++(h->args_begin());
  auto end = h->args_end();
  Expr new_body = mk<TRUE>(efac);
  ExprVector new_args, new_vars;
  unsigned int id = 0;
  for (; it != end; ++it) {
    Expr arg = *it;
    if (isOpX<GT>(arg) || isOpX<GEQ>(arg) || isOpX<LT>(arg) ||
        isOpX<LEQ>(arg) || isOpX<EQ>(arg) || isOpX<NEQ>(arg)) {
      std::string vname("VAR_");
      vname += boost::lexical_cast<std::string>(++id);
      Expr v = bind::intConst(mkTerm<std::string>(vname, efac));
      new_body = boolop::land(
          new_body,
          mk<OR>(mk<AND>(mk<EQ>(v, mkTerm(expr::mpz_class(1UL), efac)), arg),
                 mk<AND>(mk<EQ>(v, mkTerm(expr::mpz_class(0UL), efac)), mk<NEG>(arg))));
      new_args.push_back(v);
      new_vars.push_back(v);
    } else if (isOpX<PLUS>(arg) || isOpX<MINUS>(arg) || isOpX<MULT>(arg) ||
               isOpX<DIV>(arg) || isOpX<MPQ>(arg) || isOpX<MPZ>(arg)) {
      std::string vname("VAR_");
      vname += boost::lexical_cast<std::string>(++id);
      Expr v = bind::intConst(mkTerm<std::string>(vname, efac));
      new_body = boolop::land(new_body, mk<EQ>(v, arg));
      new_args.push_back(v);
      new_vars.push_back(v);
    } else {
      new_args.push_back(arg);
    }
  }
  Expr head = bind::fapp(*(h->args_begin()), new_args);
  Expr body = boolop::land(new_body, rule.body());

  boost::copy(rule.vars(), std::back_inserter(new_vars));
  HornRule new_rule(new_vars, head, body);
  return new_rule;
}

void normalizeHornClauseHeads(HornClauseDB &db) {
  std::vector<HornRule> worklist;
  boost::copy(db.getRules(), std::back_inserter(worklist));

  for (auto rule : worklist) {
    HornRule new_rule = replaceNonVarsInHead(rule);
    db.removeRule(rule);
    db.addRule(new_rule);
  }
}

void removeFiniteMapsArgsHornClausesTransf(HornClauseDB &db) {

  // return new db
  // prebuild all the predicates that need to be rewritten and rewrite all at
  // once

  ExprFactory &efac = db.getExprFactory();

  ExprVector worklist;
  boost::copy(db.getRelations(), std::back_inserter(worklist));

  // db.buildIndexes(); // how often do these indexes need to be rebuilt?, we are
                     // inserting the same clause several times, maybe update
                     // the indexes while inserting/removing a clause?

  for (auto predIt : worklist) {
    Expr predDecl = predIt;

    if (predDecl->arity() == 0) // no arguments
      continue;

      // create new relation declaration
    Expr newPredDecl = finite_map::mkMapsDecl(predDecl, efac);

    auto args = predDecl->args_begin();
    Expr predName = *args;
    errs() << "Removing args from " << *predName << "\n";

  }

  // from here on, copy the DB
  // get clauses in pred definition, requires indexes (see
  // buildIndexes())
  // auto HCDefSet = db.def(predDecl);

  // // change the rules in this predicate
  // for (auto rule : HCDefSet) {
  //   // be careful here because the rule may be a fact
  //   errs() << "Def rule: " << *(rule->get()) << "\n";
  //   const ExprVector &vars = rule->vars();
  //   ExprSet allVars(vars.begin(), vars.end());

  //   FiniteMapArgsVisitor fmav(db, allVars, predName, newPredDecl);
  //   Expr newRule = visit(fmav, rule->get());
  //   db.addRule(allVars, newRule);
  // }

  // db.buildIndexes();

  // // TODO: this set needs to be copied!!!!!, ask!!!!
  // // copy original DB, read from there.
  // auto HCUseSet = db.use(predDecl);
  // // clauses that calls this predicate (duplicated work for rec clauses unless
  // // we skip processing the body of the pred definition above)
  // for (HornRule *rule : HCUseSet) {
  //   errs() << "Calling rule: " << *(rule->get()) << "\n";
  //   const ExprVector &vars = rule->vars();
  //   ExprSet allVars(vars.begin(), vars.end());

  //   // only changes the calls in the body, adding needed unifications
  //   FiniteMapArgsVisitor fmav(db, allVars, predName, newPredDecl);
  //   // initialize it with the predicate that we want to process!! and use
  //   // only one visitor

  //   HornRule newRule(allVars, visit(fmav, rule->get()));
  //   db.addRule(newRule); // wait until the end to add and delete
  // }
  // db.registerRelation(newPredDecl);
  // // remove old relation declaration
  // // db.m_rels.remove(predIt) // (not public)
  // }
}

void removeFiniteMapsBodiesHornClausesTransf(HornClauseDB &db) {

  ExprFactory &efac = db.getExprFactory();

  std::vector<HornRule> worklist;
  boost::copy(db.getRules(), std::back_inserter(worklist));

  for (auto rule : worklist) {
    ExprVector vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());

    DagVisitCache dvc; // same for all the clauses??
    FiniteMapBodyVisitor fmv(db.getExprFactory(), allVars);

    HornRule new_rule(allVars, rule.head(), visit(fmv, rule.body(), dvc));
    db.removeRule(rule);

    db.addRule(new_rule);
  }
}


} // namespace seahorn
