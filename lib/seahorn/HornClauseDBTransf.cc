#include "seahorn/HornClauseDBTransf.hh"

#include "seahorn/Expr/ExprOpFiniteMap.hh"
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
  ScopedStats _st_("HornFmaps");

  ExprFactory &efac = tdb.getExprFactory();
  ExprMap predDeclTMap;

  Stats::start("FiniteMapTransfArgs");
  for (auto &predIt : db.getRelations()) {

    Expr newPredDecl;
    if (predIt->arity() < 2) // just return type?, is this assumption correct?
      newPredDecl = predIt;
    else {
      newPredDecl = fmap::mkMapsDecl(predIt);

      if (newPredDecl != predIt)
        predDeclTMap[predIt] = newPredDecl;
    }
    tdb.registerRelation(newPredDecl);
  }

  auto transformLemmas = [&](std::map<Expr, ExprVector> &lMap,
                             std::map<Expr, ExprVector> &lMapT) {
    for (auto &pair : lMap) {
      Expr pred = pair.first;
      ExprVector &lemmas = pair.second;

      // skip if the predicate does not need to be translated: assuming that an
      // invariant does not refer to other predicates in the program
      if (predDeclTMap.count(bind::name(pred)) == 0) {
        auto &lemmasT = lMapT[pred];
        lemmasT.insert(lemmasT.end(), lemmas.begin(), lemmas.end());
      } else {
        Expr predT = rewriteFiniteMapArgs(pred, predDeclTMap);

        for (auto &l : lemmas) {
          lMapT[predT].push_back(rewriteFiniteMapArgs(l, predDeclTMap));
        }
      }
    }
  };

  auto oconstraints = db.getAllConstraints();
  auto tconstraints = tdb.getAllConstraints();
  transformLemmas(oconstraints, tconstraints);

  auto oinvars = db.getAllInvariants();
  auto tinvars = tdb.getAllInvariants();
  transformLemmas(oinvars, tinvars);

  for (const auto &rule : db.getRules()) {
    Expr ruleE;
    if (isOpX<TRUE>(rule.body()))
      // HACK for the transformation (forcing not simplifying implication)
      ruleE = mk<IMPL>(rule.body(), rule.head());
    else
      ruleE = rule.get();

    const ExprVector &vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());
    HornRule newRule(allVars,
                     rewriteFiniteMapArgs(ruleE, allVars, predDeclTMap));
    tdb.addRule(newRule);
  }

  // copy queries
  for (auto &q : db.getQueries())
    tdb.addQuery(q);

  Stats::stop("FiniteMapTransfArgs");
}

void removeFiniteMapsBodyHornClausesTransf(HornClauseDB &db, HornClauseDB &tdb,
                                           EZ3 &zctx) {

  ZSimplifier<EZ3> zsimp(zctx);
  ExprFactory &efac = tdb.getExprFactory();

  for (const auto &rule : db.getRules()) {
    const ExprVector &vars = rule.vars();
    ExprSet allVars(vars.begin(), vars.end());
    DagVisitCache dvc;
    FiniteMapBodyVisitor fmbv(allVars, efac, zsimp);

    if (isOpX<TRUE>(rule.body()))
      tdb.addRule(rule);
    else {
      Expr body = visit(fmbv, rule.body(), dvc);

      ExprSet newVars;
      copy_if(allVars, newVars, [](Expr expr) { // not finite map
        return !isOpX<FINITE_MAP_TY>(bind::rangeTy(bind::fname(expr)));
      });
      HornRule newRule(newVars, boolop::limp(body, rule.head()));
      tdb.addRule(newRule);
    }
  }

  // copy predicates
  for (auto &predIt : db.getRelations())
    tdb.registerRelation(predIt);

  // copy queries
  for (auto &q : db.getQueries())
    tdb.addQuery(q);
}

} // namespace seahorn
