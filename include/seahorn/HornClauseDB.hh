#ifndef _HORN_CLAUSE_DB__H_
#define _HORN_CLAUSE_DB__H_
/// Horn Clause Database


#include "llvm/Support/raw_ostream.h"

#include <boost/range.hpp>
#include <boost/range/algorithm/sort.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <vector>
#include <sstream>

#include "ufo/Expr.hpp"

namespace seahorn
{
  using namespace llvm;
  using namespace expr;

  class HornClauseDB 
  {
  public:
    class Rule
    {
      ExprVector m_vars;
      Expr m_body;

    public:
      template <typename Range>
      Rule (Range &v, Expr b) : 
        m_vars (boost::begin (v), boost::end (v)), 
        m_body(b) 
      {}

      Rule (const Rule &r) : 
        m_vars (r.m_vars), m_body (r.m_body) 
      {} 

      Expr body () const {return m_body;}
      ExprVector &vars () {return m_vars;} 
    };
      
    typedef std::vector<Rule> RuleVector;
    
  private:
    ExprVector m_rels;
    ExprVector m_vars;
    RuleVector m_rules;
    Expr m_query;
    
    std::map<Expr, ExprVector> m_covers;
    
    const ExprVector &getVars ()
    {
      boost::sort (m_vars);
      m_vars.resize (std::distance (m_vars.begin (),
                                    std::unique (m_vars.begin (),
                                                 m_vars.end ())));
      return m_vars;
    }
    
    typedef HornClauseDB this_type;
    
  public:
    HornClauseDB () {}
    
    void registerRelation (Expr fdecl) {m_rels.push_back (fdecl);}
    
    const ExprVector& getRelations () {return m_rels;}
    
    template <typename Range>
    void addRule (const Range &vars, Expr body)
    {
      if (isOpX<TRUE> (body)) return;

      m_rules.push_back (Rule (vars, body));
      boost::copy (vars, std::back_inserter (m_vars));
    }
    
    RuleVector &getRules () {return m_rules;}
    
    void addQuery (Expr q) {m_query = q;}
    Expr getQuery () {return m_query;}

    /// Add cover to a predicate
    /// Adds constraint Forall V . pred -> lemma
    void addCover (Expr pred, Expr lemma)
    {
      Expr reln = bind::fname (pred);
      // JN: I'm not sure why we need to rename variables 
      /*
      ExprMap sub;
      unsigned idx = 0;
      for (auto it = ++reln->args_begin (), end = reln->args_end (); it != end; ++it)
        sub [*it] = bind::bvar (idx++, bind::typeOf (*it));
      
      m_covers [reln].push_back (replace (lemma, sub));
      */
      m_covers [reln].push_back (lemma);
    }
    
    /// Returns the current cover for the predicate
    const Expr getCover (Expr pred) 
    {
      Expr reln = bind::fname (pred);
      Expr lemma = mknary<AND> (mk<TRUE> (pred->efac ()),
                                m_covers [reln /*pred*/].begin (), 
                                m_covers [reln /*pred*/].end ());
      return lemma;
      /*      
      ExprMap sub;
      unsigned idx = 0;
      for (auto it = ++reln->args_begin (), end = reln->args_end (); 
           it != end; ++it)
      {
        Expr k = bind::bvar (idx++, bind::typeOf (*it));
        sub [k] = pred->arg (idx);
      }
          
      return replace (lemma, sub);
      */
    }

    raw_ostream& write (raw_ostream& o) const
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
    
    friend raw_ostream& operator <<(raw_ostream& o, const HornClauseDB &db)
    {
      db.write (o);
      return o;
    }
    
  };
}




#endif /* _HORN_CLAUSE_DB__H_ */
