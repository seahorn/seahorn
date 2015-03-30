#ifndef _HORN_CLAUSE_DB__H_
#define _HORN_CLAUSE_DB__H_
/// Horn Clause Database

#include "llvm/Support/raw_ostream.h"

#include <boost/range.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/lexical_cast.hpp>

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

    const ExprVector &vars () const {return m_vars;} 
        
    void setHead (Expr head) { m_head = head; }

    void setBody (Expr body) { m_body = body; }

  };


  class HornClauseDB 
  {

   private:
    typedef std::vector<HornRule> RuleVector;
    
    ExprFactory &m_efac;
    ExprVector m_rels;
    mutable ExprVector m_vars;
    RuleVector m_rules;
    Expr m_query;
    std::map<Expr, ExprVector> m_constraints;
    
    const ExprVector &getVars () const;
    
  public:

    HornClauseDB (ExprFactory &efac) : m_efac (efac) {}
    
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
    
    const RuleVector &getRules () const {return m_rules;}
    RuleVector &getRules () {return m_rules;}

    void addQuery (Expr q) {m_query = q;}
    Expr getQuery () const {return m_query;}
    bool hasQuery () const {return m_query.get () != nullptr;}
    

    bool hasConstraints (Expr reln) const {return m_constraints.count (reln) > 0;}
    
    /// Add constraint to a predicate
    /// Adds constraint Forall V . pred -> lemma
    void addConstraint (Expr pred, Expr lemma);
    
    /// Returns the current constraints for the predicate
    Expr getConstraints (Expr pred) const;
    

    raw_ostream& write (raw_ostream& o) const;

    /// load current HornClauseDB to a given FixedPoint object
    template <typename FP>
    void loadZFixedPoint (FP &fp,
                          bool skipConstraints = false,
                          bool skipQuery = false) const
    {
      for (auto &p: getRelations ())
       fp.registerRelation (p); 
      
      for (auto &rule: getRules ())
        fp.addRule (rule.vars (), rule.get ()); 
      
      for (auto &r : getRelations ())
        if (!skipConstraints && hasConstraints (r))
        {
          ExprVector args;
          for (unsigned i = 0, sz = bind::domainSz (r); i < sz; ++i)
          {
            Expr argName = mkTerm<std::string>
              ("arg_" + boost::lexical_cast<std::string> (i), m_efac);
            args.push_back (bind::mkConst (argName, bind::domainTy (r, i)));
          }
          Expr pred;
          pred = bind::fapp (r, args);
          fp.addCover (pred, getConstraints (pred));
        }
      
      if (!skipQuery && hasQuery ()) fp.addQuery (getQuery ());
    }
    
  };

  inline raw_ostream& operator <<(raw_ostream& o, const HornClauseDB &db)
  {
    db.write (o);
    return o;
  }

}
#endif /* _HORN_CLAUSE_DB__H_ */
