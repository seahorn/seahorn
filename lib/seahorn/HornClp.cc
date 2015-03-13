#include "seahorn/HornClp.hh"
#include "llvm/Support/CommandLine.h"
#include "boost/algorithm/string/replace.hpp"
#include "boost/algorithm/string/predicate.hpp"
#include "avy/AvyDebug.h"

namespace seahorn
{
  using namespace expr;
  using namespace std;

  typedef boost::unordered_map<Expr,Expr> expr_expr_map;

  struct FailNormalizer
  {
    template <typename C>
    static Expr normalize (Expr e, ExprFactory &efac, C &cache, expr_expr_map &seen)
    { std::cout << "Cannot normalize: " << *e << "\n";
      assert (0);
    }
  };

  
  template <typename M>    
  struct ExprNormalizer
  {
    template <typename C>
    static Expr normalize (Expr e, ExprFactory &efac, C &cache, expr_expr_map &seen)
    {
      assert (e);

      if (isOpX<TRUE>(e) || isOpX<FALSE>(e))  return e;
      
      /** check the cache */
      {
        typename C::const_iterator it = cache.find (e);
        if (it != cache.end ()) return it->second;
      }
      
      /** check computed table */
      {
        typename expr_expr_map::const_iterator it = seen.find (e);
         if (it != seen.end ()) return it->second;
      }
       
      Expr res;
      
      if      (isOpX<INT>(e)) { res = e; }
      else if (isOpX<MPZ>(e)) { res = e; }
      else if (isOpX<MPQ>(e))
      { return M::normalize (e, efac, cache, seen); }
      else if (bind::isBoolConst (e))
      { res = e; }
      else if (bind::isIntConst(e) ) 
      { res = e; }
      else if (bind::isRealConst(e))
      { return M::normalize (e, efac, cache, seen); }
      // we don't need to normalize arguments 
      else if (bind::isFapp (e)) { res = e; } 
      
      // -- cache the result for normalization
      if (res)
      {
        cache.insert (typename C::value_type (e, res));
        return res;
      }
      
      int arity = e->arity ();
      
      /** other terminal expressions */
      if (arity == 0) 
      {  return M::normalize (e, efac, cache, seen); }
      else if (arity == 1)
      {
        if (isOpX<UN_MINUS>(e))
        { res = mk<UN_MINUS> (normalize (e->left(), efac, cache, seen)); }
        else if (isOpX<NEG>(e))
        { res = op::boolop::lneg (normalize (e->left(), efac, cache, seen)); }
        else 
        { return M::normalize (e, efac, cache, seen); }
      }
      else if (arity == 2)
      {
        
        Expr t1 = normalize (e->left(), efac, cache, seen);
        Expr t2 = normalize (e->right(), efac, cache, seen);
        
        /** BoolOp */
        if (isOpX<AND>(e)) 
        { res = op::boolop::land (t1,t2); }
        else if (isOpX<OR>(e))
        { res = op::boolop::lor (t1,t2); }
        else if (isOpX<IMPL>(e))
        { return M::normalize (e, efac, cache, seen); }
        else if (isOpX<IFF>(e))
        { return M::normalize (e, efac, cache, seen); }
        else if (isOpX<XOR>(e))
        { return M::normalize (e, efac, cache, seen); }
        /** NumericOp */
        else if (isOpX<PLUS>(e))
        { res = mk<PLUS> (t1,t2); }
        else if (isOpX<MINUS>(e))
        { res = mk<MINUS> (t1,t2); }
        else if (isOpX<MULT>(e))
        { res = mk<MULT> (t1,t2); }
        else if (isOpX<DIV>(e))
        { res = mk<DIV> (t1,t2);}
        /** Comparisson Op */
        else if (isOpX<EQ>(e))
        { res = mk<EQ> (t1,t2); }
        else if (isOpX<NEQ>(e))
        { res = mk<NEQ> (t1,t2);}
        else if (isOpX<LEQ>(e))
        { res = mk<LEQ> (t1,t2); }
        else if (isOpX<GEQ>(e))
        { res = mk<GEQ> (t1,t2); }
        else if (isOpX<LT>(e))
        { res = mk<LT> (t1,t2); }
        else if (isOpX<GT>(e))
        { res = mk<GT> (t1,t2); }
        else
        { return M::normalize (e, efac, cache, seen); }
      }
      else if (isOpX<AND> (e) || isOpX<OR> (e) ||
               isOpX<PLUS> (e) || isOpX<MINUS> (e) ||
               isOpX<MULT> (e))
      {
        vector<Expr> args;
        for (ENode::args_iterator it = e->args_begin(), end = e->args_end();
              it != end; ++it)
        {
          Expr a = normalize (*it, efac, cache, seen);
          args.push_back (a);
        }
        
        if (isOp<AND>(e))
        { res = mknary<AND> (args.begin (), args.end ()); }
        else if (isOp<OR>(e))
        { res = mknary<OR> (args.begin (), args.end ()); }
        else if (isOp<PLUS>(e))
        { res = mknary<PLUS> (args.begin (), args.end ()); }
        else if (isOp<MINUS>(e))
        { res = mknary<MINUS> (args.begin (), args.end ()); }
        else if (isOp<MULT>(e))
        { res = mknary<MULT> (args.begin (), args.end ());  }
      }

      if (!res)
        return M::normalize (e, efac, cache, seen);
      
      assert (res);
      seen.insert (expr_expr_map::value_type (e, res ));
      return res;
    }
  }; 

  enum exprStrOp { _AND, _OR, _PLUS, _MINUS, _MULT};

  class ExprStr
  {
    string m_s;

    static string to_str (exprStrOp op)
    {
      switch (op)
      {
        case (_AND):  return ",";
        case (_OR):   return ";";
        case (_PLUS): return "+";
        case (_MINUS):return "-";
        case (_MULT): return "*";
        default: assert (false && "unreachable");
      }
    }
    
   public:

    ExprStr () {} ;
    ExprStr (string s, bool isVar=false): m_s (s) 
    {
      boost::replace_all(m_s, "%", "");
      boost::replace_all(m_s, "@", "_");
      boost::replace_all(m_s, ".", "_");

      if (isVar && !m_s.empty ())
      { m_s [0] = std::toupper(m_s [0]); }

      if (!isVar && !m_s.empty ())
      {
        m_s [0] = std::tolower(m_s [0]);
        if (m_s [0] == '_') 
        {
          // some unlikely prefix
          boost::replace_first(m_s, "_", "p___");
        }
      }

    } 

    static ExprStr True ()  { return ExprStr ("true"); }
    static ExprStr False () { return ExprStr ("false"); }

    bool empty () const { return m_s.empty (); }

    void print (ostream& o) const { o << m_s ; }

    string str () const { return m_s; }

    // build formulae
    ExprStr  operator+(ExprStr e)
    { return ExprStr ("(" + m_s + "+" + e.m_s + ")"); }
    ExprStr  operator-(ExprStr e)
    { return ExprStr ("(" + m_s + "-" + e.m_s + ")"); }
    ExprStr  operator*(ExprStr e)
    { return ExprStr ("(" + m_s + "*" + e.m_s + ")"); }
    ExprStr  operator/(ExprStr e)
    { return ExprStr ("(" + m_s + "/" + e.m_s + ")"); }
    ExprStr  operator-()
    { return ExprStr ("(0 - " + m_s + ")"); }
    ExprStr  operator~()
    { return ExprStr ("\\+(" + m_s + ")"); }
    ExprStr  operator&&(ExprStr e)
    { return ExprStr ("(" + m_s + "," + e.m_s + ")"); }
    ExprStr  operator||(ExprStr e)
    { return ExprStr ("(" + m_s + ";" + e.m_s + ")"); }
    ExprStr  operator<(ExprStr e)
    { return ExprStr ("(" + m_s + "<" + e.m_s + ")"); }
    ExprStr  operator<=(ExprStr e)
    { return ExprStr ("(" + m_s + "=<" + e.m_s + ")"); }
    ExprStr  operator==(ExprStr e)
    { return ExprStr ("(" + m_s + "=" + e.m_s + ")"); }
    ExprStr  operator>(ExprStr e)
    { return ExprStr ("(" + m_s + ">" + e.m_s + ")"); }
    ExprStr  operator>=(ExprStr e)
    { return ExprStr ("(" + m_s + ">=" + e.m_s + ")"); }
    ExprStr  operator!=(ExprStr e)
    { return ExprStr (m_s + "<" + e.m_s) || ExprStr (m_s + ">" + e.m_s); }

    static ExprStr mknary (exprStrOp op, std::vector<ExprStr> args)
    {
      if (std::distance (args.begin (), args.end ()) == 0) 
        return ExprStr ();
      typedef typename std::vector<ExprStr>::iterator iterator;
      string s = (*args.begin ()).str ();
      for(iterator it = ++ (args.begin ()), end = args.end (); it!=end ; ++it )
      {
        ExprStr arg = *it;
        s = "(" + s + to_str (op) + arg.str () + ")";
      }
      return ExprStr (s);
    }

  };
 
  typedef boost::unordered_map<Expr,ExprStr> expr_str_map;
  struct FailPrettyPrinter
  {
    template <typename C>
    static ExprStr print (Expr e, Expr parent, const ExprVector &rels, 
                          ExprFactory &efac, C &cache, expr_str_map &seen)
    { std::cout << "Cannot print: " << *e << "\n";
      assert (0);
    }
  };

  template <typename M>    
  struct ExprPrettyPrinter
  {

    static bool isTopLevelExpr (Expr e, Expr parent)
    {
      if (!parent) 
        return true;

      if (bind::isFapp (parent)) 
        return false;
      
      if (parent->arity () >= 2)
      {
        if (isOpX <AND> (parent) || isOpX<OR> (parent)) 
          return true;
      }

      return false;
    }


    // negate e if it is a literal otherwise return null
    static Expr negate (Expr e, ExprFactory &efac)
    {
      if (bind::isBoolConst (e) || bind::isIntConst (e))
        return mk<EQ>(e, mkTerm<mpz_class> (0, efac)); 
      if (isOpX<GT> (e))
        return mk<LEQ> (e->left (), e->right ());
      if (isOpX<GEQ> (e))
        return mk<LT> (e->left (), e->right ());
      if (isOpX<LT> (e))
        return mk<GEQ> (e->left (), e->right ());
      if (isOpX<LEQ> (e))
        return mk<GT> (e->left (), e->right ());
      if (isOpX<EQ> (e))
        return mk<OR> (mk<LT> (e->left (), e->right ()),
                       mk<GT> (e->left (), e->right ()));
      if (isOpX<NEQ> (e))
        return mk<EQ> (e->left (), e->right ());
      
      return NULL;
    }

    template <typename C>
    static ExprStr print (Expr e, Expr parent, const ExprVector &rels, 
                          ExprFactory &efac, C &cache, expr_str_map &seen)
                          
    {
      assert (e);

      if (isOpX<TRUE>(e))
      { 
        if (!isTopLevelExpr (e, parent))
        { return ExprStr ("1"); }
        else 
        { return ExprStr::True ();}
      }

      if (isOpX<FALSE>(e)) 
      {
        if (!isTopLevelExpr (e, parent))
        { return ExprStr ("0"); }
        else
        { return ExprStr::False (); }
      }
            
      // { /** check the cache */
      //   typename C::const_iterator it = cache.find (e);
      //   if (it != cache.end ()) return it->second;
      // }

      { /** check computed table */
        typename expr_str_map::const_iterator it = seen.find (e);
         if (it != seen.end ()) return it->second;
      }
       
      ExprStr res;
      
      if (isOpX<MPZ>(e)) 
      { 
        const MPZ& op = dynamic_cast<const MPZ&>(e->op ());
        if (op.get () < 0)
          res = ExprStr ("(" + boost::lexical_cast<std::string>(op.get()) + ")");
        else
          res = ExprStr (boost::lexical_cast<std::string>(op.get()));
      }
      else if (isOpX<MPQ>(e))
      { return M::print (e, parent, rels, efac, cache, seen); }      
      else if (bind::isBoolConst (e))
      { // e can be positive or negative
        
        ENode *fname = *(e->args_begin());
        if (isOpX<FDECL> (fname)) 
          fname = fname->arg (0);
        std::string sname = boost::lexical_cast<std::string> (fname);

        bool isVar = (std::find (rels.begin (), rels.end (), *(e->args_begin())) == rels.end ());
        if (isTopLevelExpr (e, parent) && isVar)
        { res = (ExprStr (sname, true) == ExprStr ("1")); }
        else 
        { res = ExprStr (sname, isVar ? true: false); }

      }
      else if (bind::isIntConst (e) )
      {
        Expr name = bind::name (e);
        std::string sname;
        if (isOpX<STRING> (name)) 
        {  res = ExprStr (getTerm<std::string> (name), 
                          (bind::isIntVar ? true : false)); }
        else 
        {
          ENode *fname = *(e->args_begin());
          if (isOpX<FDECL> (fname)) fname = fname->arg (0);         
          res = ExprStr (boost::lexical_cast<std::string> (fname), 
                         (bind::isIntVar ? true : false));              
        }
      }
      else if (bind::isRealConst (e))
      { return M::print (e, parent, rels, efac, cache, seen); }
      else if (bind::isFapp (e))
      {
        
        ENode *fname = *(e->args_begin());
        if (isOpX<FDECL> (fname)) 
          fname = fname->arg (0);

        string fapp = boost::lexical_cast<std::string> (fname) ;              
        ENode::args_iterator it = ++ (e->args_begin ());
        ENode::args_iterator end = e->args_end ();

        if (std::distance (it, end) > 0)
        {
          fapp += "(";
          for (; it != end; )
          {
            ExprStr arg = print (*it, e, rels, efac, cache, seen);
              fapp += arg.str (); 
              ++it;
              if (it != end)
                fapp += ",";
          }
          fapp += ")";
        }
        res = ExprStr (fapp);          
      }

      if (!res.empty ())
      { // -- cache the result for pretty printing
        // cache.insert (typename C::value_type (e, res));
        return res;
      }
      
      int arity = e->arity ();
      /** other terminal expressions */
      if (arity == 0) 
      {  return M::print (e, parent, rels, efac, cache, seen); }
      else if (arity == 1)
      {
        if (isOpX<UN_MINUS> (e))
        { res = -print (e->left(), e, rels, efac, cache, seen); }
        else if (isOpX<NEG> (e))
        { 
          Expr not_e = negate (e->left (), efac);
          if (not_e) 
          { res = print (not_e, e, rels, efac, cache, seen); }          
          else
          { res = ~print (e->left(), e, rels, efac, cache, seen); }
        }
      }          
      else if (arity == 2)
      {
        
        ExprStr s1 = print (e->left(), e, rels, efac, cache, seen);
        ExprStr s2 = print (e->right(), e, rels, efac, cache, seen);
        
        /** BoolOp */
        if (isOpX<AND> (e)) 
        { res = s1 && s2;  }
        else if (isOpX<OR>(e))
        { res = s1 || s2; }
        else if (isOpX<IMPL>(e))
        { return M::print (e, parent, rels, efac, cache, seen); }
        else if (isOpX<IFF>(e))
        { return M::print (e, parent, rels, efac, cache, seen); }
        else if (isOpX<XOR>(e))
        { return M::print (e, parent, rels, efac, cache, seen); }
        /** NumericOp */
        else if (isOpX<PLUS>(e))
        { res = s1 + s2; }
        else if (isOpX<MINUS>(e))
        { res = s1 - s2; }
        else if (isOpX<MULT>(e))
        { res = s1 * s2; }
        else if (isOpX<DIV>(e))
        { res = s1 / s2;}
        /** Comparisson Op */
        else if (isOpX<EQ>(e))
        { res = s1 == s2; }
        else if (isOpX<NEQ>(e))
        { res = s1 != s2;}
        else if (isOpX<LEQ>(e))
        { res = s1 <= s2; }
        else if (isOpX<GEQ>(e))
        { res = s1 >= s2; }
        else if (isOpX<LT>(e))
        { res = s1 < s2; }
        else if (isOpX<GT>(e))
        { res = s1 > s2; }
        else
        { return M::print (e, parent, rels, efac, cache, seen); }
      }
      else if (isOpX<AND> (e) || isOpX<OR> (e) ||
               isOpX<PLUS> (e) || isOpX<MINUS> (e) ||
               isOpX<MULT> (e))
      {
        vector<ExprStr> args;
        for (ENode::args_iterator it = e->args_begin(), end = e->args_end();
             it != end; ++it)
        {
          ExprStr a = print (*it, e, rels, efac, cache, seen);
          args.push_back (a);
        }
        
        if (isOp<AND>(e))
        { res = ExprStr::mknary (_AND, args); }
        else if (isOp<OR>(e))
        { res = ExprStr::mknary (_OR, args); }
        else if (isOp<PLUS>(e))
        { res = ExprStr::mknary (_PLUS, args); }
        else if (isOp<MINUS>(e))
        { res = ExprStr::mknary (_MINUS, args); }
        else if (isOp<MULT>(e))
        { res = ExprStr::mknary (_MULT, args);  }
        else
        {  return M::print (e, parent, rels, efac, cache, seen); }
      }
      
      assert (!res.empty());
      seen.insert (expr_str_map::value_type (e, res ));
      return res;
    }
  }; 

  void ClpRule::normalize () 
  {
    expr_expr_map seen, cache;
    Expr norm_body = ExprNormalizer<FailNormalizer>::
        normalize (m_body, m_efac, cache, seen);
    m_body = op::boolop::gather (op::boolop::nnf (norm_body));
  }

  void ClpRule::print (ostream &o) const 
  {        

    expr_str_map seen, cache;
    ExprStr str_head = ExprPrettyPrinter<FailPrettyPrinter>::
        print (m_head, NULL, m_rels, m_efac, cache, seen);    
    str_head.print (o); 

    if (isFact()) 
    { o << ".\n";  }
    else
    {
      o << " :- ";
      seen.clear ();
      ExprStr str_body = ExprPrettyPrinter<FailPrettyPrinter>::
          print (m_body, NULL, m_rels, m_efac, cache, seen);
      str_body.print (o);
      o << ".\n";
    }
  }    

  // // replace all arguments with fresh variables
  // Expr replace_args_with_vars (Expr f)
  // {
  //   assert (bind::isFapp (f));

  //   Expr reln = bind::fname (f);
  //   unsigned idx = 0;
  //   ExprVector args;
  //   for (auto it = ++reln->args_begin (), end = reln->args_end (); 
  //        it != end; ++it)
  //   {
  //     Expr k = bind::bvar (idx++, *it);
  //     args.push_back (k);
  //   }
  //   return bind::fapp (reln, args);
  // }


  ClpHornify::ClpHornify (HornClauseDB &db, ExprFactory &efac): 
      m_rels (db.getRelations ()), m_efac (efac)
  {     

    // Added false <- query as another rule
    ClpRule query (mk<FALSE> (m_efac) , mk<TRUE> (m_efac), m_efac, m_rels);
    query.addBody (db.getQuery ());
    m_rules.push_back (query);

    for (auto & rule : db.getRules ())
    {
      Expr f =  rule.body ();
      if (bind::isFapp (f))
      {  
        // TODO: add constraints
        Expr inv = mk<TRUE> (m_efac); //db.getConstraints (replace_args_with_vars (f));
        m_rules.push_back (ClpRule (f, inv, m_efac, m_rels)); 
      }
      else
      {
        assert (((f->arity () == 2) && isOpX<IMPL> (f)));

        // TODO: add constraints
        Expr inv = mk<TRUE> (m_efac); // db.getConstraints (replace_args_with_vars (f->right ()));

        ClpRule r (f->right (), f->left (),  inv, m_efac, m_rels);      
        r.normalize ();
        m_rules.push_back (r);
      }
    }
  }

  string ClpHornify::toString () const
  {
    std::ostringstream oss;
    for (auto &rule : m_rules) { rule.print (oss); }
    return oss.str ();
  }
}
