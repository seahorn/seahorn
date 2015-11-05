#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "seahorn/config.h"

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

#include "seahorn/HornifyModule.hh"

#include "llvm/Support/CommandLine.h"

#include "boost/lexical_cast.hpp"

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
    
    Expr exprFromNum( ikos::z_number n, ExprFactory &efac)
    {
      const mpz_class mpz ((mpz_class) n);
      return mkTerm (mpz, efac);
    }
    
    Expr exprFromIntVar( varname_t v, ExprFactory &efac)
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

  // From ufo
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

      // XXX AG: Something does not like ITE expressions. Perhaps MathSat
      // iterprets them as non-logical ITEs
      //return mk<ITE> (c, t, e);
       return boolop::lor (boolop::land (c, t), 
			   boolop::land (mk<NEG>(c), e));
    }

    Expr exprFromCons(lincons_t lincons, theory_t *theory, ExprFactory &efac)
    {
      Expr lhs = exprFromTerm(theory->get_term(lincons), theory, efac);
      Expr rhs = exprFromCst(theory->get_constant(lincons), theory, efac);
      
      return theory->is_strict (lincons) ? mk<LT>(lhs, rhs) : mk<LEQ>(lhs, rhs);
    }

    Expr exprFromCst (constant_t cst, theory_t *theory, ExprFactory &efac)
    {
      mpq_class v;
      // XXX We know that the theory is tvpi, use its method direclty.
      tvpi_cst_set_mpq (v.get_mpq_t (), (tvpi_cst_t)cst);
      return mkTerm(v,efac);
    }

    Expr exprFromTerm (linterm_t term, theory_t *theory, ExprFactory &efac)
    {
      std::vector<Expr> coeffs (theory->term_size (term));

      for(size_t i = 0;i < coeffs.size (); i++)
	coeffs[i] = lmult (exprFromCst (theory->term_get_coeff (term,i), 
                                          theory, efac),
                             mkTerm(varMap->lookup
                                    (theory->term_get_var(term,i)), 
                                    efac));

      return coeffs.size() > 1 ? 
	mknary<PLUS> (coeffs.begin (), coeffs.end ()) : coeffs [0];
    }

    Expr lmult(Expr cst, Expr var)
    {
      // Check if cst is equal to 1
      const MPQ& op = dynamic_cast<const MPQ&>(cst->op ());
      return op.get () == 1 ? var :  mk<MULT>(cst,var);
    }
 
  };

} // end namespace crab_llvm


namespace seahorn
{
  using namespace llvm;
  using namespace crab::cfg_impl;
  
  bool LoadCrab::runOnModule (Module &M)
  {
    for (auto &F : M) runOnFunction (F);
    return true;
  }
  
  expr::Expr Convert (crab_llvm::CrabLlvm &crab,
                      const llvm::BasicBlock *BB, 
                      const expr::ExprVector &live, 
                      expr::ExprFactory &efac) 
  {
    expr::Expr e = nullptr;

    auto absDomWrapperPtr = crab [BB];

    if (absDomWrapperPtr->getId () == crab_llvm::GenericAbsDomWrapper::id_t::boxes) {
      crab_llvm::boxes_domain_t boxes;
      crab_llvm::getAbsDomWrappee (absDomWrapperPtr, boxes);        
      crab_llvm::LDDToExpr t = crab_llvm::LDDToExpr (&boxes);
      e = t.toExpr (boxes.getLdd (), efac);
    }
    else if (absDomWrapperPtr->getId () == crab_llvm::GenericAbsDomWrapper::id_t::arr_boxes) {
      crab_llvm::arr_boxes_domain_t inv;
      crab_llvm::getAbsDomWrappee (absDomWrapperPtr, inv);        
      crab_llvm::boxes_domain_t boxes = inv.get_base_domain ();
      crab_llvm::LDDToExpr t = crab_llvm::LDDToExpr (&boxes);
      e = t.toExpr (boxes.getLdd (), efac);
    }
    else { 
      // --- any other domain is translated to convex linear
      //     constraints
      crab_llvm::LinConstToExpr t;
      e = t.toExpr (absDomWrapperPtr->to_linear_constraints (), efac);
    }
        
    if ( (std::distance (live.begin (), 
                         live.end ()) == 0) && (!expr::isOpX<expr::FALSE> (e))) {
      e = expr::mk<expr::TRUE> (efac); 
    }

    assert (e);

    return e;
  }

  bool LoadCrab::runOnFunction (Function &F)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    crab_llvm::CrabLlvm &crab = getAnalysis<crab_llvm::CrabLlvm> ();
    
    auto &db = hm.getHornClauseDB ();
    
    for (auto &BB : F)
    {
      // skip all basic blocks that HornifyModule does not know
      if (! hm.hasBbPredicate (BB)) continue;
      
      const ExprVector &live = hm.live (BB);
      
      Expr pred = hm.bbPredicate (BB);
      Expr inv = Convert (crab, &BB, live, hm.getExprFactory ());

      LOG ("crab", 
           errs () << "Loading invariant " << *bind::fname (pred);
           errs () << "("; for (auto v: live) errs () << *v << " ";
           errs () << ")  "  << *inv << "\n"; );
           

      db.addConstraint (bind::fapp (pred, live), inv);
      
    }
    return true;
  }
  
  
  void LoadCrab::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<HornifyModule> ();
    AU.addRequired<crab_llvm::CrabLlvm> ();
  }
  
}
#endif
