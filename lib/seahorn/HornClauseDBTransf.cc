#include "seahorn/HornClauseDBTransf.hh"
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
                 mk<AND>(mk<EQ>(v, mkTerm(expr::mpz_class(0UL), efac)),
                         mk<NEG>(arg))));
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

template <typename Set, typename Predicate>
void copy_if(Set &src, Set &dst, Predicate shouldCopy) {
  for (auto it : src)
    if (shouldCopy(it))
      dst.insert(it);
}

// -- tdb is an empty db that will contain db after transformation
void removeFiniteMapsHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb) {

  ExprFactory &efac = tdb.getExprFactory();
  ExprMap predDeclTransf;

  // Remove Finite Maps arguments
  for (auto &predIt : db.getRelations()) {

    Expr newPredDecl;
    if (predIt->arity() < 2) // just return type?, is this assumption correct?
      newPredDecl = predIt;
    else {
      // create new relation declaration
      newPredDecl = finite_map::mkMapsDecl(predIt, efac);

      if (newPredDecl != predIt)
        predDeclTransf[predIt] = newPredDecl;
    }
    tdb.registerRelation(newPredDecl); // register relation in transformed db
  }

  for (const auto &rule : db.getRules()) {
    const ExprVector &vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());
    DagVisitCache dvc; // TODO: same for all the clauses?
    FiniteMapArgsVisitor fmav(allVars, predDeclTransf, efac);
    Expr newRule = visit(fmav, rule.get(), dvc);
    tdb.addRule(allVars, newRule);
  }

  // copy queries
  for (auto &q : db.getQueries())
    tdb.addQuery(q);

  // Remove Finite Maps from Bodies
  std::vector<HornRule> worklist;
  boost::copy(tdb.getRules(), std::back_inserter(worklist));

  for (auto rule : worklist) {
    ExprVector vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());

    DagVisitCache dvc; // same for all the clauses?
    FiniteMapBodyVisitor fmv(allVars, efac);

    Expr body = visit(fmv, rule.body(), dvc);

    ExprSet newVars;
    copy_if(allVars, newVars, [](Expr expr) { // not finite map
      return !isOpX<FINITE_MAP_TY>(bind::rangeTy(bind::fname(expr)));
    });

    HornRule new_rule(newVars, rule.head(), body);

    tdb.removeRule(rule);
    tdb.addRule(new_rule);
  }
}

} // namespace seahorn
