#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "seahorn/config.h"

#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
  using namespace llvm;

  /// Loads Crab invariants into  a Horn Solver
  class LoadCrab: public llvm::ModulePass
  {

  public:
    static char ID;
    
    LoadCrab () : ModulePass(ID) {}
    virtual ~LoadCrab () {}
    
    virtual bool runOnModule (Module &M);
    virtual bool runOnFunction (Function &F);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "LoadCrab";}
  };
  
  char LoadCrab::ID = 0;
  Pass* createLoadCrabPass () {return new LoadCrab ();}

} // end namespace seahorn

#ifndef HAVE_CRAB_LLVM
// dummy implementation when Crab is not compiled in
namespace seahorn
{
  void LoadCrab::getAnalysisUsage (AnalysisUsage &AU) const
  {AU.setPreservesAll ();}

  bool LoadCrab::runOnModule (Module &M)
  {
    errs () << "WARNING: Not loading invariants. Compiled without Crab support.\n";
    return false;
  }
  bool LoadCrab::runOnFunction (Function &F) {return false;}
}
#else
  // real implementation starts here 
#include "ufo/Expr.hpp"
#include "ufo/ExprLlvm.hpp"

#include <crab_llvm/CfgBuilder.hh>
#include <crab_llvm/CrabLlvm.hh>
#include <crab_llvm/AbstractDomains.hh>

#include "seahorn/HornifyModule.hh"
#include "llvm/Support/CommandLine.h"

namespace llvm
{
   template <typename Number, typename VariableName>
   llvm::raw_ostream& operator<< (llvm::raw_ostream& o, 
                                  crab::cfg_impl::z_lin_cst_t cst)
   {
     std::ostringstream s;
     s << cst;
     o << s.str ();
     return o;
   }

   inline llvm::raw_ostream& operator<< (llvm::raw_ostream& o, 
                                         crab::cfg_impl::z_lin_cst_sys_t csts)
   {
     std::ostringstream s;
     s << csts;
     o << s.str ();
     return o;
   }

} // end namespace


namespace crab_llvm
{
  using namespace llvm;
  using namespace expr;
  using namespace crab::cfg_impl;

  // Conversion from linear constraints to Expr
  struct LinConstToExpr
  {
    // Crab does not distinguish between bools and the rest of
    // integers but SeaHorn does.
    
    // A normalizer for Boolean constraints
    class BoolCst 
    {
      typedef enum {T_TRUE, T_FALSE, T_TOP} tribool_t;
      
      tribool_t      m_val;
      
      // internal representation:
      // constraint is of the form m_coef*m_var {<=,==} m_rhs
      // m_coef and m_rhs can be negative numbers.
      
      ikos::z_number m_coef;
      const Value*   m_var;
      bool           m_is_eq; //tt:equality, ff:inequality
      ikos::z_number m_rhs;
      
     public:
      
      // If cst is a constraint of the form x<=c where x is a LLVM
      // Value of type i1 then return x, otherwise null.
      static const Value* isBoolCst (z_lin_cst_t cst)
      {
        if (cst.is_disequation ()) return nullptr;
        auto e = cst.expression() - cst.expression().constant();
        if (std::distance (e.begin (), e.end ()) != 1) return nullptr; 
        auto t = *(e.begin ());
        varname_t v = t.second.name();
        assert (v.get () && "Cannot have shadow vars");
        if ( (*(v.get ()))->getType ()->isIntegerTy (1))
          return *(v.get ()); 
        else return nullptr; 
      }
      
      BoolCst (z_lin_cst_t cst): m_val (T_TOP),
                                 m_coef (0), m_rhs (0), 
                                 m_var (nullptr), m_is_eq (cst.is_equality ())
      {
        assert (isBoolCst (cst));
        
        auto e = cst.expression() - cst.expression().constant();
        auto t = *(e.begin ());
        assert (t.second.name ().get () && "Cannot have shadow vars");
        m_var  = *(t.second.name ().get ());
        m_coef = t.first;
        m_rhs  = -cst.expression().constant();
        
        if (m_is_eq)
        {
          if (m_rhs == 0)                        /* k*x == 0 for any k*/
          { m_val = T_FALSE; }
          else if (m_coef == 1 && m_rhs == 1)    /*x == 1*/
          { m_val = T_TRUE; }
          else if (m_coef == -1 && m_rhs == -1)  /*-x == -1*/
          { m_val = T_TRUE; }
        }
      }
      
      // Conjoin two boolean constraints
      void operator+= (BoolCst other)
      {
        // they cannot disagree otherwise the initial constraint
        // would be false.
        assert (!(m_val == T_TRUE  && other.m_val == T_FALSE));
        assert (!(m_val == T_FALSE && other.m_val == T_TRUE));
        
        if (m_val != T_TOP && other.m_val == T_TOP) 
          return; 
        if (m_val == T_TOP && other.m_val != T_TOP)
        { 
          m_val = other.m_val; 
          return;  
        }
        
        if (!m_is_eq && !other.m_is_eq) // both are inequalities
        {
          
          if ( ( (m_coef == 1 && m_rhs == 0) &&               /* x <= 0*/
                 (other.m_coef == -1 && other.m_rhs == 0)) || /*-x <= 0*/ 
               ( (m_coef == -1 && m_rhs == 0) &&              /*-x <= 0*/
                 (other.m_coef == 1 && other.m_rhs == 0)))    /* x <= 0*/
          { m_val = T_FALSE; }
          else if ( ((m_coef == 1 && m_rhs == 1) &&                /*x <= 1*/
                     (other.m_coef == -1 && other.m_rhs == -1)) || /*-x <=-1*/ 
                    ((m_coef == -1 && m_rhs == -1) &&              /*-x <=-1*/
                     (other.m_coef == 1 && other.m_rhs == 1)))     /*x <= 1*/
          {  m_val = T_TRUE; } 
        }
      }
      
      bool isUnknown () const { return m_val == T_TOP; }
      
      Expr toExpr (ExprFactory &efac) const 
      {
        if (isUnknown ()) return mk<TRUE>(efac);
        
        Expr e = mkTerm<const Value*>(m_var, efac);
        e = bind::boolConst (e);
        if (m_val == T_FALSE) return mk<NEG> (e);
        else return e;
        }
      
    };
      

    typedef DenseMap<const Value*, BoolCst> bool_map_t;
    bool_map_t bool_map;
    
    static Expr exprFromNum( ikos::z_number n, ExprFactory &efac)
    {
      const mpz_class mpz ((mpz_class) n);
      return mkTerm (mpz, efac);
    }
    
    static Expr exprFromIntVar( varname_t v, ExprFactory &efac)
    {
      assert (v.get () && "Cannot have shadow vars");
      Expr e = mkTerm<const Value*>(*(v.get()), efac);
      return bind::intConst (e);
    }
    
    Expr toExpr (z_lin_cst_t cst, ExprFactory &efac)
    {
      if (cst.is_tautology ())     
        return mk<TRUE> (efac);
      
      if (cst.is_contradiction ()) 
        return mk<FALSE> (efac);

      // booleans
      if (const Value* v = BoolCst::isBoolCst (cst))
      {
        BoolCst b2 (cst);
        auto it = bool_map.find (v);
        if (it != bool_map.end ())
        {
          BoolCst &b1 = it->second;
          b1 += b2;
        }
        else { bool_map.insert (make_pair (v, b2)); } 
        
        return mk<TRUE> (efac); // we ignore cst for now
      }
      
      // integers
      auto e = cst.expression() - cst.expression().constant();
      Expr ee = exprFromNum ( ikos::z_number ("0"), efac);
      for (auto t : e)
      {
        ikos::z_number n  = t.first;
        varname_t v = t.second.name();
        if (n == 0) continue;
        else if (n == 1) 
          ee = mk<PLUS> (ee, exprFromIntVar (v, efac));
        else if (n == -1) 
          ee = mk<MINUS> (ee, exprFromIntVar (v, efac));
        else
          ee = mk<PLUS> (ee, mk<MULT> ( exprFromNum (n, efac), 
                                        exprFromIntVar (v, efac)));
      }
      
      ikos::z_number c = -cst.expression().constant();
      Expr cc = exprFromNum (c, efac);
      if (cst.is_inequality ())
        return mk<LEQ> (ee, cc);
      else if (cst.is_equality ())
        return mk<EQ> (ee, cc);        
      else 
        return mk<NEQ> (ee, cc);
      
    }
    
    Expr toExpr (z_lin_cst_sys_t csts, ExprFactory &efac)
    {
      Expr e = mk<TRUE> (efac);
      
      // integers
      for (auto cst: csts)
      { e = boolop::land (e, toExpr (cst, efac)); } 
      
      // booleans 
      for (auto p: bool_map)
      {
        auto b = p.second;
        if (!b.isUnknown ()) { e = boolop::land (e, b.toExpr (efac)); }
      }
      
      return e;
    }
  };

  #ifdef HAVE_LDD
  // Conversion from Ldd to Expr
  class LDDToExpr
  {
  public:
    struct VarMap
    {
      virtual ~VarMap () {}
      virtual const Value *lookup (int i) const = 0;
    };
    
    template <typename T>
    class VarMapT : public VarMap
    {
      const T *vm;
      
    public:
      VarMapT (const T *m) : vm (m) {}
      const Value *lookup (int i) const { 
        auto V = vm->getVarName (i).get (); 
        assert (V);
        return *V;
      }
    };

  protected:
    boost::shared_ptr<VarMap> varMap;
  public:

    template <typename T>
    LDDToExpr (const T *vm) : 
      varMap(new VarMapT<T>(vm)) {}

    Expr toExpr (LddNodePtr n, ExprFactory &efac)
    {
      LddManager *ldd = getLddManager (n);
      
      LddNode *N = Ldd_Regular(&(*n));
      if (Ldd_GetTrue (ldd) == N)
	return &*n == N ? mk<TRUE>(efac) : mk<FALSE>(efac);
      
      /** cache holds pointers because anything that is placed in the
	  cache will not disapear until 'n' is deleted */
      std::map<LddNode*, Expr> cache; 
      Expr res = toExprRecur(ldd, &*n, efac, cache);
      return res;
    }

  protected: 
    Expr toExprRecur(LddManager* ldd, LddNode* n, 
                     ExprFactory &efac, std::map<LddNode*, Expr> &cache)
    {

      LddNode *N = Ldd_Regular (n);
      Expr res(NULL);

      if (N == Ldd_GetTrue (ldd)) res = mk<TRUE> (efac);
      else if (N->ref != 1)
	{
          std::map<LddNode*,Expr>::const_iterator it = cache.find (N);
	  if (it != cache.end ()) res = it->second;
	}

      if (res) return N == n ? res : boolop::lneg (res);

      Expr c = exprFromCons (Ldd_GetCons(ldd, N), 
                             Ldd_GetTheory (ldd), efac);
      res = lite (c, 
		  toExprRecur (ldd, Ldd_T (N), efac, cache),
		  toExprRecur (ldd, Ldd_E (N), efac, cache));

      if (N->ref != 1) cache [N] = res;
      
      return n == N ? res : boolop::lneg (res);
    }

    Expr lite (Expr c, Expr t, Expr e)
    {
      if (t == e) return t;
      if (isOpX<TRUE> (c)) return t;
      if (isOpX<FALSE> (c)) return e;
      if (isOpX<TRUE> (t) && isOpX<FALSE> (e)) return c;
      if (isOpX<TRUE> (e) && isOpX<FALSE> (t)) return boolop::lneg (c);
      return mk<ITE> (c, t, e);
      // return boolop::lor (boolop::land (c, t), 
      //                     boolop::land (mk<NEG>(c), e));
    }

    Expr exprFromCons(lincons_t lincons, theory_t *theory, ExprFactory &efac)
    {
      Expr lhs = exprFromTerm(theory->get_term(lincons), theory, efac);
      Expr rhs = exprFromIntCst(theory->get_constant(lincons), theory, efac);
      
      return theory->is_strict (lincons) ? mk<LT>(lhs, rhs) : mk<LEQ>(lhs, rhs);
    }

    Expr exprFromIntCst (constant_t cst, theory_t *theory, ExprFactory &efac)
    {
      mpq_class v;
      // XXX We know that the theory is tvpi, use its method directly.
      tvpi_cst_set_mpq (v.get_mpq_t (), (tvpi_cst_t) cst);
      const mpz_class n((mpz_class) v);
      return mkTerm (n, efac);
    }

    Expr exprFromIntVar (int v, ExprFactory &efac) {
      return bind::intConst (mkTerm (varMap->lookup(v), efac));
    }

    Expr exprFromTerm (linterm_t term, theory_t *theory, ExprFactory &efac)
    {
      std::vector<Expr> coeffs (theory->term_size (term));

      for(size_t i = 0;i < coeffs.size (); i++)
	coeffs[i] = lmult (exprFromIntCst (theory->term_get_coeff (term,i), 
                                             theory, efac),
                             exprFromIntVar (theory->term_get_var (term,i), 
                                             efac));
                                          

      return coeffs.size() > 1 ? 
	mknary<PLUS> (coeffs.begin (), coeffs.end ()) : coeffs [0];
    }

    Expr lmult(Expr cst, Expr var)
    {
      // Check if cst is equal to 1
      const MPZ& op = dynamic_cast<const MPZ&>(cst->op ());
      return op.get () == 1 ? var :  mk<MULT>(cst,var);
    }
   };
   #endif 

   // Conversion from domain of disjunctive intervals to Expr
   class DisIntervalToExpr
   {
     typedef typename dis_interval_domain_t::interval_t interval_t;
     typedef typename dis_interval_domain_t::varname_t varname_t;
     typedef typename dis_interval_domain_t::number_t number_t;
     
    public:
     
     Expr toExpr (dis_interval_domain_t inv, ExprFactory &efac)
     {
       Expr e = mk<TRUE> (efac);
        for (auto p: boost::make_iterator_range (inv.begin (), inv.end ())) {
          Expr d = mk<FALSE> (efac);
          for (auto i: boost::make_iterator_range (p.second.begin (), p.second.end ())) {
            d = boolop::lor (d, intervalToExpr (p.first, i, efac));
          }
          e = boolop::land (e, d);
        }
        return e;
     }
     
    private:   
     
     Expr intervalToExpr (varname_t v, interval_t i, ExprFactory &efac) {
       
       if (i.is_top ())
         return mk<TRUE> (efac);
       
       if (i.is_bottom ())
         return mk<FALSE> (efac);
       
       if (i.lb ().is_finite () && i.ub ().is_finite ()) {
         auto lb = *(i.lb ().number());
         auto ub = *(i.ub ().number());
         if (lb == ub) {
           return mk<EQ> (LinConstToExpr::exprFromIntVar (v, efac),
                          LinConstToExpr::exprFromNum (lb, efac));
         }
         else {
           return mk<AND> (mk<GEQ> (LinConstToExpr::exprFromIntVar (v, efac), 
                                    LinConstToExpr::exprFromNum (lb, efac)),
                           mk<LEQ> (LinConstToExpr::exprFromIntVar (v, efac), 
                                    LinConstToExpr::exprFromNum (ub, efac)));
         }
       }
       
        if (i.lb ().is_finite ()) {
         auto lb = *(i.lb ().number());
          return mk<GEQ> (LinConstToExpr::exprFromIntVar (v, efac), 
                          LinConstToExpr::exprFromNum (lb, efac));
        }
        
        assert (i.ub ().is_finite ());
        
        auto ub = *(i.ub ().number());
        return mk<LEQ> (LinConstToExpr::exprFromIntVar (v, efac), 
                        LinConstToExpr::exprFromNum (ub, efac));
        
      }    
   };

} // end namespace crab_llvm


namespace seahorn
{
  using namespace llvm;
  using namespace crab;
  using namespace crab::cfg_impl;
  using namespace crab_llvm;
  using namespace expr;
  
  #ifdef HAVE_LDD
  namespace expr_cnf {

     // Decides whether an expression represents a variable/constant
     class IsVar : public std::unary_function<Expr,bool>
     {
      private:
       /** list of exception expressions that are not treated as variables */
       ExprSet m_except;
      public:
       IsVar () {}
       IsVar (const ExprSet& except) : m_except (except) {}
       IsVar (const IsVar &o) : m_except (o.m_except) {}
       IsVar &operator= (IsVar o)
       {
         swap (*this, o);
      return *this;
       }
       
       /** add an exception expression */
       void exception (Expr e) { m_except.insert (e); }
       
       bool operator () (Expr e)
       {
         if (m_except.count (e) > 0) return false;
         
         // -- variant
         if (isOpX<VARIANT> (e))
           return true;
         // -- old-style constants
         if (bind::isBoolVar (e) || bind::isIntVar (e) || bind::isRealVar (e))
           return true;
         // -- new-style constants 
         if (bind::isBoolConst (e) || bind::isIntConst (e) || bind::isRealConst (e))
           return true;
         return false;
       }
     };
  
     // Return the set of variables in exp
     ExprSet getVars (Expr exp) {
       ExprSet s;
       filter (exp, IsVar (), std::inserter (s, s.begin ()));
       return s;
     }
  
     Expr mkRelation (ExprSet allVars, string fname, ExprFactory& efac) {
       ExprVector sorts;
       sorts.reserve (allVars.size () + 1);
       for (auto &v : allVars) {
         //assert (bind::isFapp (v));
         //assert (bind::domainSz (bind::fname (v)) == 0);
         sorts.push_back (bind::typeOf (v));
       }
       
       sorts.push_back (mk<BOOL_TY> (efac));
       Expr name = mkTerm (fname, efac);
       Expr decl = bind::fdecl (name, sorts);
       return decl;
     }

     // Convert e to CNF using a ZFixedPoint
     Expr cnf (EZ3 & zctx, ExprFactory &efac, Expr phi) {

       if (isOpX<FALSE> (phi)  || isOpX<TRUE> (phi))
         return phi;

       // Add two horn rules in fp
       // --- phi -> h
       // --- h and not phi -> false
       //
       // The solution is returned in cnf
       
       ZFixedPoint<EZ3> fp (zctx);
       ExprSet allVars = getVars (phi); 
       // -- register predicates
       Expr decl_h = mkRelation (allVars, "h",  efac);
       ExprSet emptyVars;
       Expr decl_p = mkRelation (emptyVars, "p",  efac);
       fp.registerRelation (decl_h);
       fp.registerRelation (decl_p);
       // -- add rules
       Expr h = bind::fapp (decl_h, allVars);
       Expr p = bind::fapp (decl_p, emptyVars);
       Expr r1 = mk<IMPL> (phi, h);
       fp.addRule (allVars, r1);
       Expr r2 = mk<IMPL> (mk<AND> (h, mk<NEG> (phi)), p);
       fp.addRule (allVars, r2);
       Expr r3 = mk<IMPL> (mk<FALSE> (efac), p);
       fp.addRule (emptyVars, r3);
       
       // -- add query
       fp.addQuery (h);
       
       LOG ("crab-cnf", errs () << "Content of fixedpoint: " << fp << "\n";);
       boost::tribool status = fp.query ();
       LOG ("crab-cnf", 
            if (status || !status) errs () << "result=" << fp.getAnswer () << "\n";);
       assert (status);
       
       Expr res = fp.getCex ();
       LOG ("crab-cnf", errs () << "Cnf=" << *res << "\n";);
       
       return res;
     }
  } // end namespace
  #endif 

  Expr CrabInvToExpr (GenericAbsDomWrapperPtr absVal,
                      const ExprVector &live, 
                      EZ3& zctx,
                      ExprFactory &efac) 
  {
    Expr e = mk<TRUE> (efac);

    #ifdef HAVE_LDD
    // --- translation of linear decision diagrams
    if (absVal->getId () == GenericAbsDomWrapper::id_t::boxes) {
      boxes_domain_t boxes;
      getAbsDomWrappee (absVal, boxes);        
      LDDToExpr t = LDDToExpr (&boxes);
      e = t.toExpr (boxes.getLdd (), efac);
      //e = expr_cnf::cnf (zctx, efac, e);
    }
    else if (absVal->getId () == GenericAbsDomWrapper::id_t::arr_boxes) {
      arr_boxes_domain_t inv;
      getAbsDomWrappee (absVal, inv);        
      boxes_domain_t boxes = inv.get_base_domain ();
      LDDToExpr t = LDDToExpr (&boxes);
      e = t.toExpr (boxes.getLdd (), efac);
      //e = expr_cnf::cnf (zctx, efac, e);
    }
    else 
    #endif 
    { 
      // --- translation of disjunctive interval constraints
      if (absVal->getId () == GenericAbsDomWrapper::id_t::dis_intv) {
        dis_interval_domain_t inv;
        getAbsDomWrappee (absVal, inv);        
        DisIntervalToExpr t;
        e = t.toExpr (inv, efac);
      }
      else if (absVal->getId () == GenericAbsDomWrapper::id_t::arr_dis_intv) {
        arr_dis_interval_domain_t inv;
        getAbsDomWrappee (absVal, inv);        
        DisIntervalToExpr t;
        e = t.toExpr (inv.get_base_domain (), efac);
      }
      else {
        // --- translation to convex linear constraints
        LinConstToExpr t;
        e = t.toExpr (absVal->to_linear_constraints (), efac);
      }
    }
        
    if ( (std::distance (live.begin (), 
                         live.end ()) == 0) && (!isOpX<FALSE> (e))) {
      e = mk<TRUE> (efac); 
    }

    return e;
  }

  bool LoadCrab::runOnModule (Module &M)
  {
    for (auto &F : M) 
      runOnFunction (F);

    return true;
  }

  bool LoadCrab::runOnFunction (Function &F)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    CrabLlvm &crab = getAnalysis<CrabLlvm> ();
    
    auto &db = hm.getHornClauseDB ();
    
    for (auto &BB : F)
    {
      // skip all basic blocks that HornifyModule does not know
      if (! hm.hasBbPredicate (BB)) continue;
      
      const ExprVector &live = hm.live (BB);
      
      Expr pred = hm.bbPredicate (BB);

      Expr exp = CrabInvToExpr (crab [&BB], live, hm.getZContext (), hm.getExprFactory ());

      LOG ("crab", 
           errs () << "Loading invariant " << *bind::fname (pred);
           errs () << "("; for (auto v: live) errs () << *v << " ";
           errs () << ")  "  << *exp << "\n"; );
           

      db.addConstraint (bind::fapp (pred, live), exp);
      
    }
    return true;
  }
  
  
  void LoadCrab::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<HornifyModule> ();
    AU.addRequired<CrabLlvm> ();
  }
  
} // end namespace seahorn
#endif
