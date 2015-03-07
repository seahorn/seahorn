#include "seahorn/HornClp.hh"
#include "llvm/Support/CommandLine.h"
#include "boost/algorithm/string/replace.hpp"

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
    static Expr negate (Expr e, ExprFactory &efac)
    {
      if (isOpX<TRUE>(e))
        return mk<FALSE>(efac);
      else if (isOpX<FALSE>(e))
        return mk<TRUE>(efac);
      else if (isOpX<EQ>(e))
        return mk<NEQ>(e->left (), e->right ());
      else if (isOpX<NEQ>(e))
        return mk<EQ>(e->left (), e->right ());
      else if (isOpX<LEQ>(e))
        return mk<GT>(e->left (), e->right ());
      else if (isOpX<GEQ>(e))
        return mk<LT>(e->left (), e->right ());
      else if (isOpX<LT>(e))
        return mk<GEQ>(e->left (), e->right ());
      else if (isOpX<GT>(e))
        return mk<LEQ>(e->left (), e->right ());
      return NULL;
    }

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
        {
          Expr e1 = normalize (e->left(), efac, cache, seen);
          res = negate (e1, efac); 
          if (!res) res = op::boolop::lneg (e1);
        }
        else 
          return M::normalize (e, efac, cache, seen);
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
        else
        {  return M::normalize (e, efac, cache, seen); }
      }
      
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
        m_s [0] = std::toupper(m_s [0]);
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
    { return ExprStr ("-(" + m_s + ")"); }
    ExprStr  operator~()
    { return ExprStr ("\\+(" + m_s + ")"); }
    ExprStr  operator&&(ExprStr e)
    { return ExprStr ("(" + m_s + "," + e.m_s + ")"); }
    ExprStr  operator||(ExprStr e)
    { return ExprStr ("(" + m_s + ";" + e.m_s + ")"); }
    ExprStr  operator<(ExprStr e)
    { return ExprStr ("(" + m_s + "<" + e.m_s + ")"); }
    ExprStr  operator<=(ExprStr e)
    { return ExprStr ("(" + m_s + "<=" + e.m_s + ")"); }
    ExprStr  operator==(ExprStr e)
    { return ExprStr ("(" + m_s + "=" + e.m_s + ")"); }
    ExprStr  operator>(ExprStr e)
    { return ExprStr ("(" + m_s + ">" + e.m_s + ")"); }
    ExprStr  operator>=(ExprStr e)
    { return ExprStr ("(" + m_s + ">=" + e.m_s + ")"); }
    ExprStr  operator!=(ExprStr e)
    { return ExprStr ("(" + m_s + "<>" + e.m_s + ")"); }

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
    static ExprStr print (Expr e, ExprFactory &efac, C &cache, expr_str_map &seen)
    { std::cout << "Cannot print: " << *e << "\n";
      assert (0);
    }
  };

  template <typename M>    
  struct ExprPrettyPrinter
  {


    template <typename C>
    static ExprStr print (Expr e, ExprFactory &efac, C &cache, expr_str_map &seen)
    {
      assert (e);

      if (isOpX<TRUE>(e))  return ExprStr::True ();
      if (isOpX<FALSE>(e)) return ExprStr::False ();
            
      { /** check the cache */
        typename C::const_iterator it = cache.find (e);
        if (it != cache.end ()) return it->second;
      }
      { /** check computed table */
        typename expr_str_map::const_iterator it = seen.find (e);
         if (it != seen.end ()) return it->second;
      }
       
      ExprStr res;
      
      if (isOpX<INT>(e)) 
      { res = ExprStr (boost::lexical_cast<std::string>(e.get())); }
      else if (isOpX<MPZ>(e)) 
      { 
        const MPZ& op = dynamic_cast<const MPZ&>(e->op ());
        res = ExprStr (boost::lexical_cast<std::string>(op.get()));
      }
      else if (isOpX<MPQ>(e))
      { return M::print (e, efac, cache, seen); }
      else if (bind::isBoolConst (e))
      {
        ENode *fname = *(e->args_begin());
        if (isOpX<FDECL> (fname)) 
          fname = fname->arg (0);
        res = ExprStr (boost::lexical_cast<std::string> (fname));
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
      { return M::print (e, efac, cache, seen); }
      else if (bind::isFapp (e))
      {
        
        ENode *fname = *(e->args_begin());
        if (isOpX<FDECL> (fname)) 
          fname = fname->arg (0);

        //string fapp = "'" + boost::lexical_cast<std::string> (fname) + "'";              
        string fapp = boost::lexical_cast<std::string> (fname) ;              
        ENode::args_iterator it = ++ (e->args_begin ());
        ENode::args_iterator end = e->args_end ();
        if (it != end)
        {
          fapp += "(";
          for (; it != end; )
          {
            ExprStr arg = print (*it, efac, cache, seen);
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
        cache.insert (typename C::value_type (e, res));
        return res;
      }
      
      int arity = e->arity ();
      /** other terminal expressions */
      if (arity == 0) 
      {  return M::print (e, efac, cache, seen); }
      else if (arity == 1)
      {
        if (isOpX<UN_MINUS> (e))
        { res = -print (e->left(), efac, cache, seen); }
        else if (isOpX<NEG> (e))
        { res = ~print (e->left(), efac, cache, seen); }
        else 
        { return M::print (e, efac, cache, seen); }
      }
      else if (arity == 2)
      {
        
        ExprStr s1 = print (e->left(), efac, cache, seen);
        ExprStr s2 = print (e->right(), efac, cache, seen);
        
        /** BoolOp */
        if (isOpX<AND> (e)) 
        { res = s1 && s2;  }
        else if (isOpX<OR>(e))
        { res = s1 || s2; }
        else if (isOpX<IMPL>(e))
        { return M::print (e, efac, cache, seen); }
        else if (isOpX<IFF>(e))
        { return M::print (e, efac, cache, seen); }
        else if (isOpX<XOR>(e))
        { return M::print (e, efac, cache, seen); }
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
        { return M::print (e, efac, cache, seen); }
      }
      else if (isOpX<AND> (e) || isOpX<OR> (e) ||
               isOpX<PLUS> (e) || isOpX<MINUS> (e) ||
               isOpX<MULT> (e))
      {
        vector<ExprStr> args;
        for (ENode::args_iterator it = e->args_begin(), end = e->args_end();
             it != end; ++it)
        {
          ExprStr a = print (*it, efac, cache, seen);
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
        {  return M::print (e, efac, cache, seen); }
      }
      
      assert (!res.empty());
      seen.insert (expr_str_map::value_type (e, res ));
      return res;
    }
  }; 

  void ClpRule::normalize () 
  {
    expr_expr_map seen, cache;
    Expr norm_body = ExprNormalizer<FailNormalizer>::normalize (m_body, m_efac, cache, seen);
    m_body = op::boolop::gather (op::boolop::nnf (norm_body));
  }

  void ClpRule::print (ostream &o) const 
  {        

    expr_str_map seen, cache;
    ExprStr str_head = ExprPrettyPrinter<FailPrettyPrinter>::print (m_head, m_efac, cache, seen);    
    str_head.print (o); 

    if (isFact())
    { o << ".\n"; }
    else
    {
      o << " :-\n";
      seen.clear ();
      ExprStr str_body = ExprPrettyPrinter<FailPrettyPrinter>::print (m_body, m_efac, cache, seen);
      str_body.print (o);
      o << ".\n";
    }
  }    

  ClpHornify::ClpHornify (HornClauseDB &db, ExprFactory &efac): 
      m_efac (efac)
  { 

    // Added false <- query as another rule
    ClpRule query (mk<FALSE> (m_efac) , m_efac);
    query.addBody (db.getQuery ());
    m_rules.push_back (query);

    for (auto & rule : db.getRules ())
    {
      Expr f =  rule.body ();

      if (bind::isFapp (f))
        m_rules.push_back (ClpRule (f, m_efac));
      else
      {
        if (!((f->arity () == 2) && isOpX<IMPL> (f)))
        { 
          cout << "Warning: hornClp ignoring clause " << *f << "\n"; 
          continue; 
        }

        assert (((f->arity () == 2) && isOpX<IMPL> (f)));
        ClpRule r (f->right (), f->left (), m_efac);      
        r.normalize ();
        m_rules.push_back (r);

      }
    }
  }

  string ClpHornify::toString () const
  {
    std::ostringstream oss;
    for (auto &rule : m_rules)
    { rule.print (oss); }
    return oss.str ();
  }
}
