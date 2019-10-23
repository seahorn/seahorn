#include "seahorn/ClpWrite.hh"
#include "llvm/Support/CommandLine.h"
#include "llvm/IR/Value.h"
#include "llvm/IR/Constants.h"
#include "seahorn/Expr/ExprLlvm.hh"
#include "boost/algorithm/string/replace.hpp"
#include "boost/algorithm/string/predicate.hpp"
#include "seahorn/Support/SeaDebug.h"
#include <unordered_map>

static llvm::cl::opt<bool>
PrintClpFapp ("horn-clp-fapp",
              llvm::cl::desc ("Print function applications in CLP format"), 
              llvm::cl::init (false),
              llvm::cl::Hidden);

namespace seahorn
{
  using namespace expr;
  using namespace std;
  using namespace llvm;

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
    { return (*this < e) || (*this > e); }

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
 
  typedef std::unordered_map<Expr,ExprStr> expr_str_map;
  struct FailPrettyPrinter
  {
    template <typename C, typename Range>
    static ExprStr print (Expr e, Expr parent, const Range &rels, 
                          ExprFactory &efac, C &cache, expr_str_map &seen)
    { std::cout << "Cannot print: " << *e << "\n";
      assert (false);
      return ExprStr ();
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
        return mk<EQ>(e, mkTerm<expr::mpz_class> (0UL, efac)); 
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

    template <typename C, typename Range>
    static ExprStr print (Expr e, Expr parent, const Range &rels, 
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
        expr::mpz_class op = getTerm<expr::mpz_class>(e);
        if (op < 0UL)
          res = ExprStr ("(" + op.to_string() + ")");
        else
          res = ExprStr (op.to_string());
      }
      else if (isOpX<MPQ>(e))
      { return M::print (e, parent, rels, efac, cache, seen); }      
      else if (bind::isBoolConst (e))
      { // e can be positive or negative
        Expr fname = bind::fname (bind::fname (e));
        std::string sname = boost::lexical_cast<std::string> (fname);
        bool isVar = (std::find (std::begin (rels), std::end (rels), bind::fname (e)) == rels.end ());
        if (isTopLevelExpr (e, parent) && isVar)
        { res = (ExprStr (sname, true) == ExprStr ("1")); }
        else 
        { res = ExprStr (sname, isVar); }
      }
      else if (bind::isIntConst (e) )
      {
        Expr fname = bind::fname (bind::fname (e));        
        res = ExprStr (boost::lexical_cast<std::string> (fname), true); 
      }
      else if (bind::isRealConst (e))
      { return M::print (e, parent, rels, efac, cache, seen); }
      else if (bind::isFapp (e))
      {
        Expr fname = bind::fname (bind::fname (e));
        string fapp = boost::lexical_cast<std::string> (fname) ;              
        auto it = ++ (e->args_begin ());
        auto end = e->args_end ();

        if (std::distance (it, end) > 0)
        {
          fapp += (PrintClpFapp ? "(" : "-[");
          for (; it != end; )
          {
            ExprStr arg = print (*it, e, rels, efac, cache, seen);
              fapp += arg.str (); 
              ++it;
              if (it != end)
                fapp += ",";
          }
          fapp += (PrintClpFapp ? ")" : "]");
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
        for (auto it = e->args_begin(), end = e->args_end();
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

  void ClpWrite::ClpRule::normalize () 
  { m_body = op::boolop::gather (op::boolop::nnf (m_body)); }

  void ClpWrite::ClpRule::print (ostream &o) const 
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


  ClpWrite::ClpWrite (HornClauseDB &db, ExprFactory &efac): 
    m_rels (db.getRelations ()), m_efac (efac)
  {     

    for (auto q:  db.getQueries ())
    {
      // Added false <- query as another rule
      ClpRule query (mk<FALSE> (m_efac) , mk<TRUE> (m_efac), m_efac, m_rels);
      query.addBody (q);
      m_rules.push_back (query);
    }

    for (auto & rule : db.getRules ())
    {
      // TODO: add constraints
      Expr inv = mk<TRUE> (m_efac); // db.getConstraints (replace_args_with_vars (f->right ()));
      ClpRule r (rule.head (), rule.body (), inv, m_efac, m_rels);      
      r.normalize ();
      m_rules.push_back (r);
    }
  }

  string ClpWrite::toString () const
  {
    std::ostringstream oss;
    for (auto &rule : m_rules) { rule.print (oss); }
    return oss.str ();
  }
}
