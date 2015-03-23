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

  class HornRule
  { 
    ExprVector m_vars;
    Expr m_head;
    Expr m_body; 
    
   public:
    template <typename Range>
    HornRule (Range &v, Expr b) : 
        m_vars (boost::begin (v), boost::end (v)), 
        m_head (b), m_body (mk<TRUE>(b->efac ())) 
    {
      if ((b->arity () == 2) && isOpX<IMPL> (b))
      { 
        m_body = b->left ();
        m_head = b->right ();
      }
      else 
      { assert (bind::isFapp (b)); }      
    }
    
    HornRule (const HornRule &r) : 
        m_vars (r.m_vars), m_head (r.m_head), m_body (r.m_body) 
    {} 
    
    // return only the body of the horn clause
    Expr body () const {return m_body;}

    // return only the head of the horn clause
    Expr head () const {return m_head;}
    
    // return the implication body => head
    Expr get () const 
    { 
      if (isOpX<TRUE> (m_body)) 
        return m_head;
      else 
        return mk<IMPL> (m_body, m_head);
    }

    ExprVector &vars () {return m_vars;} 
        
    void setHead (Expr head) { m_head = head; }

    void setBody (Expr body) { m_body = body; }

  };


  class HornClauseDB 
  {

   private:
    typedef std::vector<HornRule> RuleVector;
    
    ExprVector m_rels;
    ExprVector m_vars;
    RuleVector m_rules;
    Expr m_query;
    std::map<Expr, ExprVector> m_constraints;
    
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
    
    const ExprVector& getRelations () const {return m_rels;}
    bool hasRelation (Expr fdecl) const
    {return std::find
        (m_rels.begin (), m_rels.end (), fdecl) != m_rels.end ();}
    
    
    template <typename Range>
    void addRule (const Range &vars, Expr rule)
    {
      if (isOpX<TRUE> (rule)) return;
      m_rules.push_back (HornRule (vars, rule));
      boost::copy (vars, std::back_inserter (m_vars));
    }
    
    RuleVector &getRules () {return m_rules;}

    void addQuery (Expr q) {m_query = q;}
    Expr getQuery () {return m_query;}

    /// Add constraint to a predicate
    /// Adds constraint Forall V . pred -> lemma
    void addConstraint (Expr pred, Expr lemma)
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
    
    /// Returns the current constraints for the predicate
    const Expr getConstraints (Expr pred) 
    {
      assert (bind::isFapp (pred));

      Expr reln = bind::fname (pred);
      assert (hasRelation (reln));

      Expr lemma = mknary<AND> (mk<TRUE> (pred->efac ()),
                                m_constraints [reln].begin (), 
                                m_constraints [reln].end ());
      ExprMap sub;
      unsigned idx = 0;
      for (auto it = ++pred->args_begin (), end = pred->args_end (); it != end; ++it)
      {
        Expr k = bind::bvar (idx++, bind::typeOf (*it));
        sub [k] = pred->arg (idx);
      }
          
      return replace (lemma, sub);
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
        
  };

  inline raw_ostream& operator <<(raw_ostream& o, const HornClauseDB &db)
  {
    db.write (o);
    return o;
  }

}
#endif /* _HORN_CLAUSE_DB__H_ */
