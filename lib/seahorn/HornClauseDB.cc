#include "seahorn/HornClauseDB.hh"

#include <boost/range.hpp>
#include <boost/range/algorithm/sort.hpp>
#include <boost/range/algorithm/copy.hpp>

#include <sstream>

namespace seahorn
{
  const ExprVector &HornClauseDB::getVars ()
  {
    boost::sort (m_vars);
    m_vars.resize (std::distance (m_vars.begin (),
                                  std::unique (m_vars.begin (),
                                               m_vars.end ())));
    return m_vars;
  }

  void HornClauseDB::addConstraint (Expr pred, Expr lemma)
  {
    assert (bind::isFapp (pred));

    if (isOpX<TRUE> (lemma)) return;
      
    Expr reln = bind::fname (pred);
    assert (hasRelation (reln));
      
    ExprMap sub;
    unsigned idx = 0;
    for (auto it = ++pred->args_begin (), end = pred->args_end (); it != end; ++it)
      sub [*it] = bind::bvar (idx++, bind::typeOf (*it));
      
    m_constraints [reln].push_back (replace (lemma, sub));
  }

  Expr HornClauseDB::getConstraints (Expr pred) const
  {
    assert (bind::isFapp (pred));

    Expr reln = bind::fname (pred);
    assert (hasRelation (reln));

    if (m_constraints.count (reln) <= 0) return mk<TRUE> (pred->efac ());
    
    Expr lemma = mknary<AND> (mk<TRUE> (pred->efac ()),
                              m_constraints.at (reln).begin (), 
                              m_constraints.at (reln).end ());
    ExprMap sub;
    unsigned idx = 0;
    for (auto it = ++pred->args_begin (), end = pred->args_end (); it != end; ++it)
    {
      Expr k = bind::bvar (idx++, bind::typeOf (*it));
      sub [k] = pred->arg (idx);
    }
          
    return replace (lemma, sub);
  }
  
  raw_ostream& HornClauseDB::write (raw_ostream& o) const
  {
    std::ostringstream oss;
    oss << "Predicates:\n;";
    for (auto &p : m_rels)
    { oss << p << "\n"; }
    oss << "Clauses:\n;";
    for (auto &r : m_rules)
    { oss << r.body () << "\n"; }
    oss << "Query:\n;";
    oss << m_query << "\n";
    o << oss.str ();
    o.flush ();
    return o;
  }

}
