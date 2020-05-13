#include "seahorn/HornClauseDB.hh"

#include <boost/range.hpp>
#include <boost/algorithm/string/predicate.hpp>
#include <boost/range/algorithm/sort.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/lexical_cast.hpp>

#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Support/SeaDebug.h"

#include <sstream>

namespace seahorn
{

  void HornClauseDB::resetIndexes ()
  {
    m_body_idx.clear ();
    m_head_idx.clear ();
  }
  
  void HornClauseDB::buildIndexes ()
  {
    resetIndexes ();
      
    /// update indexes
    for (HornRule &r : m_rules)
    {
      // -- update head index
      m_head_idx [bind::fname (r.head ())].insert (&r);
      // -- update body index
      ExprVector use;
      r.used_relations (*this, std::back_inserter (use));
      for (Expr decl : use) m_body_idx[decl].insert (&r);

    }
  }

  void HornClauseDBCallGraph::buildCallGraph ()
  {
    // indexes must be first computed
    m_db.buildIndexes ();
    
    for (auto p: m_db.getRelations ())
    {
      // -- callees
      HornClauseDB::expr_set_type callees;
      const boost::container::flat_set<HornRule*>& uses = m_db.use(p);
      for (const HornRule* r: uses)
      { callees.insert(bind::fname(r->head())); }
      m_callees.insert(std::make_pair(p, callees));

      // -- callers
      HornClauseDB::expr_set_type callers;
      const boost::container::flat_set<HornRule*>& defs = m_db.def(p);
      for (const HornRule* r: defs)
        filter (r->body (), HornClauseDB::IsRelation(m_db),
                std::inserter(callers, callers.begin())); 
      m_callers.insert(std::make_pair(p, callers));

      LOG("horn-cg", 
          errs () << *(bind::fname(p)) << "\n"
          << "\tNumber of callers=" << callers.size() << "\n"
          << "\tNumber of callees=" << callees.size() << "\n";
          if (!callers.empty()) {
            errs () << "\tCALLERS=";
            for (auto c: callers) {
              errs () << *(bind::fname(c)) << "  ";
            }
            errs () << "\n";
          }
          if (!callees.empty()) {
            errs () << "\tCALLEES=";
            for (auto c: callees) {
              errs ()  << *(bind::fname(c)) << "  ";
            }
            errs () << "\n";
          });
    }

    // XXX: we are looking for a predicate that corresponds to the
    // entry block of main. It is not enough to search for a predicate
    // with no callers since predicates from each function entry won't
    // have callers.
    for (auto p: m_db.getRelations ())
    {
      Expr fname = bind::fname(p);
      std::string sname = boost::lexical_cast<std::string> (fname);
      if (boost::starts_with(sname, "main") && callers(p).size() == 0) { 
        m_cg_entry = p;
        break;
      }
    }

    LOG("horn-cg", 
        errs () << "Entry=" << *(bind::fname(m_cg_entry)) << "\n";);
  }

  const ExprVector &HornClauseDB::getVars () const
  {
    boost::sort (m_vars);
    m_vars.resize (std::distance (m_vars.begin (),
                                  std::unique (m_vars.begin (),
                                               m_vars.end ())));
    return m_vars;
  }

  template<typename LemmaMap, typename ExprSet>
  void addLemma (LemmaMap &m, const ExprSet &rels, Expr pred, Expr lemma)
  {
    assert (bind::isFapp (pred));

    if (isOpX<TRUE> (lemma)) return;
      
    Expr reln = bind::fname (pred);
    assert (rels.count(reln) > 0);
      
    ExprMap sub;
    unsigned idx = 0;
    for (auto it = ++pred->args_begin (), end = pred->args_end (); it != end; ++it)
      sub [*it] = bind::bvar (idx++, bind::typeOf (*it));
      
    m[reln].push_back (replace (lemma, sub));
  }

  template<typename LemmaMap, typename ExprSet>
  Expr getLemmas (const LemmaMap &m, const ExprSet &rels, Expr pred) 
  {
    assert (bind::isFapp (pred));

    Expr reln = bind::fname (pred);
    assert (rels.count(reln) > 0);

    if (m.count (reln) <= 0) return mk<TRUE> (pred->efac ());
    
    Expr lemma = mknary<AND> (mk<TRUE> (pred->efac ()),
                              m.at (reln).begin (), m.at (reln).end ());
    ExprMap sub;
    unsigned idx = 0;
    for (auto it = ++pred->args_begin (), end = pred->args_end (); it != end; ++it)
    {
      Expr k = bind::bvar (idx++, bind::typeOf (*it));
      sub [k] = pred->arg (idx);
    }
          
    return replace (lemma, sub);
  }
  

  void HornClauseDB::addConstraint (Expr pred, Expr lemma)
  {
    addLemma(m_constraints, m_rels, pred, lemma);
  }

  Expr HornClauseDB::getConstraints (Expr pred) const
  {
    return getLemmas(m_constraints, m_rels, pred);
  }

  void HornClauseDB::addInvariant (Expr pred, Expr lemma)
  {
    addLemma(m_invariants, m_rels, pred, lemma);
  }

  Expr HornClauseDB::getInvariants (Expr pred) const
  {
    return getLemmas(m_invariants, m_rels, pred);
  }
  
  raw_ostream& HornClauseDB::write (raw_ostream& o) const
  {
    std::ostringstream oss;
    oss << "Predicates:\n";
    for (auto &p : m_rels)
    { oss << p << "\n"; }
    oss << "Clauses:\n";
    for (auto &r : m_rules)
    { oss << r.head () << " <- " << r.body () << ".\n"; }
    oss << "Queries:\n";
    for (auto &q : m_queries)
    { oss << q << "\n"; }
    o << oss.str ();
    o.flush ();
    return o;
  }

  HornClauseDB::horn_set_type HornClauseDB::m_empty_set;
  HornClauseDB::expr_set_type HornClauseDBCallGraph::m_expr_empty_set;

  Expr extractTransitionRelation(HornRule r, HornClauseDB &db)
  {
    Expr ruleBody = r.body();
    ExprMap body_map;
    ExprVector body_pred_apps;
    get_all_pred_apps(ruleBody, db, std::back_inserter(body_pred_apps));

    for (Expr p : body_pred_apps)
      body_map.insert (std::make_pair (p, mk<TRUE> (p->efac ())));

    Expr body_constraints = replace(ruleBody, body_map);
    return body_constraints;
  }

  bool hasBvarInRule(HornRule r, HornClauseDB &db,
                          std::map<Expr, ExprVector> currentCandidates)
  {
    ExprVector pred_vector;
    get_all_pred_apps(r.body(), db, std::back_inserter(pred_vector));
    pred_vector.push_back(r.head());

    for (Expr pred : pred_vector)
    {
      ExprVector term_vec = currentCandidates.find(bind::fname(pred))->second;
      if(term_vec.size() > 1 || (term_vec.size() == 1 && !isOpX<TRUE>(term_vec[0])))
        return true;
    }
    return false;
  }

}
