#ifndef _HORN_CLAUSE_DB__H_
#define _HORN_CLAUSE_DB__H_
/// Horn Clause Database

#include "llvm/Support/raw_ostream.h"

#include <boost/range.hpp>
#include <boost/range/algorithm/copy.hpp>
#include <boost/lexical_cast.hpp>
#include <boost/container/flat_set.hpp>

#include "ufo/Expr.hpp"
#include "seahorn/Support/Stats.hh"

#include <algorithm>
#include <map>

namespace seahorn
{
  using namespace llvm;
  using namespace expr;

  class HornClauseDB;
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

    template <typename Range>
    HornRule (Range &v, Expr head, Expr body) :
      m_vars (boost::begin (v), boost::end (v)),
      m_head (head), m_body (body)
    { }

    HornRule (const HornRule &r) :
      m_vars (r.m_vars),
      m_head (r.m_head), m_body (r.m_body)
    {}

    size_t hash () const
    {
      size_t res = expr::hash_value (m_head);
      boost::hash_combine (res, m_body);
      boost::hash_combine (res, boost::hash_range (m_vars.begin (),
                                                   m_vars.end ()));
      return res;
    }

    bool operator==(const HornRule & other) const
    { return hash() == other.hash ();}

    bool operator<(const HornRule & other) const
    { return hash() < other.hash ();}

    // return only the body of the horn clause
    Expr body () const {return m_body;}

    /// set body of the horn clause
    void setBody (Expr v) {m_body = v;}

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

    template<typename OutputIterator>
    void used_relations (HornClauseDB &db, OutputIterator out);
  };


  class HornClauseDB
  {
    friend class HornRule;
  public:

    typedef std::vector<HornRule> RuleVector;
    typedef boost::container::flat_set<Expr> expr_set_type;
    struct IsRelation : public std::unary_function<Expr, bool>
    {
      const HornClauseDB &m_db;
      IsRelation (const HornClauseDB &db) : m_db (db) {}

      bool operator() (Expr e)
      {return bind::isFdecl (e) && m_db.hasRelation (e);}
    };
  private:

    ExprFactory &m_efac;
    expr_set_type m_rels;
    mutable ExprVector m_vars;
    RuleVector m_rules;
    ExprVector m_queries;
    std::map<Expr, ExprVector> m_constraints;
    std::map<Expr, ExprVector> m_invariants;

    /// indexes


    typedef boost::container::flat_set<HornRule*> horn_set_type;
    typedef std::map<Expr, horn_set_type > index_type;
    /// maps a relation to rules it appears in the body
    index_type m_body_idx;
    /// maps a relation to rules it appears in the head
    index_type m_head_idx;

    const ExprVector &getVars () const;

    /// empty set sentinel
    static horn_set_type m_empty_set;

    /// resets all indexes
    void resetIndexes ();

  public:

    HornClauseDB (ExprFactory &efac) : m_efac (efac) {}

    ExprFactory &getExprFactory () {return m_efac;}

    void registerRelation (Expr fdecl) {m_rels.insert (fdecl);}
    const expr_set_type& getRelations () const {return m_rels;}
    bool hasRelation (Expr fdecl) const
    { return m_rels.count (fdecl) > 0; }
    /// number of relational predicates
    unsigned relSize () { return m_rels.size ();}

    /// -- build use/def indexes
    void buildIndexes ();

    /// -- returns rules that use fdecl
    /// -- i.e., rules in which fdecl appears in the body
    /// -- requires indexes (see buildIndexes())
    const horn_set_type &use (Expr fdecl) const
    {
      auto it = m_body_idx.find (fdecl);
      if (it == m_body_idx.end ()) return m_empty_set;
      return it->second;
    }

    /// -- returns rules that define fdecl
    /// -- i.e., rules in which fdecl appears in the head
    /// -- requires indexes (see buildIndexes())
    const horn_set_type &def (Expr fdecl) const
    {
      auto it = m_head_idx.find (fdecl);
      if (it == m_head_idx.end ()) return m_empty_set;
      return it->second;
    }

    template <typename Range>
    void addRule (const Range &vars, Expr rule)
    {
      if (isOpX<TRUE> (rule)) return;
      assert(std::all_of(boost::begin(vars), boost::end(vars),
                         bind::IsConst()));
      addRule (HornRule (vars, rule));
    }

    void addRule (const HornRule &rule)
    {
      m_rules.push_back (rule);
      boost::copy (rule.vars (), std::back_inserter (m_vars));
      resetIndexes ();

    }

    const ExprVector &getVars ()
    {
      // -- remove duplicates
      std::sort (m_vars.begin (), m_vars.end ());
      m_vars.erase (std::unique (m_vars.begin (), m_vars.end ()), m_vars.end ());

      return m_vars;
    }

    void removeRule (const HornRule &r)
    {
      m_rules.erase (std::remove (m_rules.begin(), m_rules.end(), r));
      resetIndexes ();
    }


    const RuleVector &getRules () const {return m_rules;}
    RuleVector &getRules () {return m_rules;}

    void addQuery (Expr q) {m_queries.push_back (q);}
    ExprVector getQueries () const {return m_queries;}
    bool hasQuery () const {return !m_queries.empty ();}


    bool hasConstraints (Expr reln) const {return m_constraints.count (reln) > 0;}

    /// Add constraint to a predicate
    /// Adds constraint Forall V . pred -> lemma
    void addConstraint (Expr pred, Expr lemma);

    /// Returns the current constraints for the predicate
    Expr getConstraints (Expr pred) const;

    bool hasInvariants (Expr reln) const {return m_invariants.count (reln) > 0;}

    /// Add invariant to a predicate
    /// Adds invariant Forall V . pred -> lemma
    void addInvariant (Expr pred, Expr lemma);

    /// Returns the current invariants for the predicate
    Expr getInvariants (Expr pred) const;


    raw_ostream& write (raw_ostream& o) const;

    /// load current HornClauseDB to a given FixedPoint object
    template <typename FP>
    void loadZFixedPoint (FP &fp,
                          bool skipConstraints = false,
                          bool skipQuery = false) const
    {
      ScopedStats _st_("HornClauseDB::loadZFixedPoint");
      for (auto &p: getRelations ())
        fp.registerRelation (p);

      for (auto &rule: getRules ())
        fp.addRule (rule.vars (), rule.get ());

      for (auto &r : getRelations ())
        if (!skipConstraints && (hasConstraints (r) || hasInvariants (r)))
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
	  if (hasConstraints (r))
	    fp.addCover (pred, getConstraints (pred));
	  if (hasInvariants (r))
	    fp.addInvariant (pred, getInvariants (pred));
        }

      if (!skipQuery) fp.addQueries (getQueries ());
    }


  };

  template<typename OutputIterator>
  void HornRule::used_relations (HornClauseDB &db, OutputIterator out)
  {filter (body (), HornClauseDB::IsRelation(db), out);}

  inline raw_ostream& operator <<(raw_ostream& o, const HornClauseDB &db)
  {
    db.write (o);
    return o;
  }

  class HornClauseDBCallGraph
  {
    /// callgraph
    typedef std::map<Expr, HornClauseDB::expr_set_type > callgraph_type;
    callgraph_type m_callers;
    callgraph_type m_callees;
    Expr m_cg_entry;

    /// empty set sentinel
    static HornClauseDB::expr_set_type m_expr_empty_set;

  public:
    HornClauseDB& m_db;
    HornClauseDBCallGraph (HornClauseDB &db) : m_db (db), m_cg_entry(mk<FALSE>(db.getExprFactory ())) {}

    /// -- build call graph
    void buildCallGraph ();

    /// -- returns an entry point of the call graph.
    bool hasEntry () const { return !isOpX<FALSE>(m_cg_entry); }
    Expr entry () const { assert(hasEntry()); return m_cg_entry; }

    /// -- requires callgraph (buildCallGraph())
    const HornClauseDB::expr_set_type& callees (Expr fdecl) const
    {
      auto it = m_callees.find (fdecl);
      if (it == m_callees.end ()) return m_expr_empty_set;
      return it->second;
    }

    /// -- requires callgraph (buildCallGraph())
    const HornClauseDB::expr_set_type& callers (Expr fdecl) const
    {
      auto it = m_callers.find (fdecl);
      if (it == m_callers.end ()) return m_expr_empty_set;
      return it->second;
    }
  };

  /*
   * This function is to extract transition relation in a rule.
   */
  Expr extractTransitionRelation(HornRule r, HornClauseDB &db);

  struct IsPredApp : public std::unary_function<Expr, bool>
  {
    HornClauseDB &m_db;
    IsPredApp (HornClauseDB &db) : m_db (db) {}

    bool operator() (Expr e)
    {return bind::isFapp (e) && m_db.hasRelation (bind::fname(e));}
  };

  struct IsBVar : public std::unary_function<Expr, bool>
  {
    IsBVar () {}
    bool operator() (Expr e)
    {return bind::isBVar (e);}
  };

  struct IsInteger : public std::unary_function<Expr, bool>
  {
    IsInteger() {}
    bool operator() (Expr e)
    {return bind::isIntConst (e);}
  };

  struct IsBoolean : public std::unary_function<Expr, bool>
  {
    IsBoolean() {}
    bool operator() (Expr e)
    {return bind::isBoolConst (e);}
  };

  template<typename OutputIterator>
  void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out)
  {filter (e, IsPredApp(db), out);}

  template<typename OutputIterator>
  void get_all_bvars (Expr e, OutputIterator out)
  {filter (e, IsBVar(), out);}

  template<typename OutputIterator>
  void get_all_integers(Expr e, OutputIterator out)
  {filter (e, IsInteger(), out);}

  template<typename OutputIterator>
  void get_all_booleans(Expr e, OutputIterator out)
  {filter (e, IsBoolean(), out);}

  /*
   * Return false if there are no bvars in all predicates in a rule, else return true.
   */
  bool hasBvarInRule(HornRule r, HornClauseDB &db,
                          std::map<Expr, ExprVector> currentCandidates);

}
#endif /* _HORN_CLAUSE_DB__H_ */
