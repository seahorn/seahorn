#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/ADT/DenseSet.h"
#include "llvm/Support/raw_ostream.h"
#include "seahorn/config.h"
#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
  using namespace llvm;

  /// Loads Crab invariants into a Horn Solver
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
/// Dummy implementation when Crab is not compiled in
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
/// Real implementation starts here 
#include "ufo/Expr.hpp"
#include "ufo/ExprLlvm.hpp"

#include "seahorn/HornifyModule.hh"
#include "seahorn/SymExec.hh"
#include "seahorn/Transforms/Instrumentation/ShadowMemDsa.hh"

#include "llvm/Support/CommandLine.h"

#include <crab_llvm/CfgBuilder.hh>
#include <crab_llvm/CrabLlvm.hh>
#include <crab_llvm/AbstractDomains.hh>

namespace crab_llvm
{
  using namespace llvm;
  using namespace expr;
  using namespace crab::cfg_impl;
  using namespace seahorn;

  // Conversion from linear constraints to Expr.
  //
  // TODO: a linear constraint is precisely translated only if all its
  // variables can be mapped to llvm Value. Otherwise, it is
  // translated to true. For instance, Crab generates shadow variables
  // representing DSA nodes that are not translated with the exception
  // of global singletons.
  class LinConstToExpr
  {

   public:

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

        if (!(v.get()))
          return nullptr;

        if ( (*(v.get ()))->getType ()->isIntegerTy (1))
          return *(v.get ()); 
        else 
          return nullptr; 
      }
      
      BoolCst (z_lin_cst_t cst): m_val (T_TOP),
                                 m_coef (0), m_rhs (0), 
                                 m_var (nullptr), m_is_eq (cst.is_equality ())
      {
        assert (isBoolCst (cst));
        
        auto e = cst.expression() - cst.expression().constant();
        auto t = *(e.begin ());
        assert (t.second.name ().get ());

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

   private:

    CrabLlvm* m_crab;
    const llvm::BasicBlock* m_bb;
    const ExprVector& m_live;

    DenseSet<const Value*> m_live_values; // for fast queries

    public:

    LinConstToExpr (CrabLlvm* crab, const llvm::BasicBlock* bb, const ExprVector &live): 
        m_crab (crab), m_bb (bb), m_live (live) { 

      for (auto v: m_live) 
      {
        Expr u = bind::fname (bind::fname (v));
        if (isOpX<VALUE> (u)) 
          m_live_values.insert (getTerm <const Value*> (u));
      }

    }      
    
    typedef DenseMap<const Value*, BoolCst> bool_map_t;
    bool_map_t bool_map;
    
    Expr exprFromNum (ikos::z_number n, ExprFactory &efac)
    {
      const mpz_class mpz ((mpz_class) n);
      return mkTerm (mpz, efac);
    }
    
    Expr exprFromIntVar (varname_t v, ExprFactory &efac)
    {
      if (!(v.get ())) {
        // Skip for now crab shadow variables.

        // TODO: v.get() method only returns a non-null value if v
        // contains a const Value*. Otherwise, it means that v refers
        // to a shadow variable which is not currently translated.
        return nullptr; 
      }

      const Value* V = *(v.get());

      if (const Value* Gv = 
          m_crab->getMemAnalysis().getRegion(*(const_cast <Function*> (m_bb->getParent ())), 
                                             const_cast<Value*> (V)).getSingleton ()) 
      {
        /// -- The crab variable v corresponds to a global singleton
        ///    cell so we can grab a llvm Value from it. We search for
        ///    the seahorn shadow variable that matches it.
        for (auto l: m_live) {
          Expr u = bind::fname (bind::fname (l));
          if (isOpX<VALUE> (u)) {
            // u is a constant
            const Value* U = getTerm <const Value*> (u);
            const Value *Scalar;
            if (shadow_dsa::isShadowMem (*U, &Scalar)) {
              if (Scalar == Gv) {
                return bind::intConst (mkTerm<const Value*> (U, efac));
              }
            }
          }
          else if (isOpX<op::SELECT> (u)) {
            // u is a constant with name v[scalar]
            Expr idx = u->right ();
            if (isOpX<VALUE> (idx)) {
              const Value* Idx = getTerm <const Value*> (idx);
              if (Idx == Gv)
                return bind::intConst (u);
            }
          }
        }
        // We could not translate the global singleton cell
        return nullptr;
      } 
      else 
      {
        // -- If here then v can be mapped directly to a llvm value
        //    after we check v is live. This is needed because we do
        //    not currently project the abstract domain onto the live
        //    variables before translation.
        if (m_live_values.count (V) > 0) {
          return bind::intConst (mkTerm<const Value*> (V, efac));
        } else {
          return nullptr; 
        }
      }
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
        if (n == 0) continue;
        
        Expr v = exprFromIntVar (t.second.name(), efac);
        if (!v) { 
          // We could not translate Crab variable.
          return mk<TRUE> (efac);
        }

        if (n == 1) {
          ee = mk<PLUS> (ee, v);
        }
        else if (n == -1)  {
          ee = mk<MINUS> (ee, v);
        } else {
          ee = mk<PLUS> (ee, mk<MULT> (exprFromNum (n, efac), v)); 
        }
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
  // Conversion from Ldd to Expr.
  // 
  // TODO: a ldd is precisely translated only if all its variables can
  // be mapped to llvm Value. Unlike in class LinConstToExpr here we
  // do not even translate global singletons.
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
        varMap(new VarMapT<T>(vm)) { }
    
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
      if (!res) 
        return mk<TRUE> (efac);
      else
        return res;
    }
    
   protected: 

    Expr toExprRecur(LddManager* ldd, LddNode* n, 
                     ExprFactory &efac, std::map<LddNode*, Expr> &cache)
    {
      
      LddNode *N = Ldd_Regular (n);
      Expr res = nullptr;
      
      if (N == Ldd_GetTrue (ldd)) 
      {
        res = mk<TRUE> (efac);
      } 
      else if (N == Ldd_GetFalse (ldd)) 
      {
        res = mk<FALSE> (efac);
      } 
      else if (N->ref != 1) 
      {
        std::map<LddNode*,Expr>::const_iterator it = cache.find (N);
        if (it != cache.end ()) res = it->second;
      }
      
      if (res) return (N == n ? res : boolop::lneg (res));

      Expr c = exprFromCons (Ldd_GetCons (ldd, N), 
                             Ldd_GetTheory (ldd), efac);

      // This should not happen because we project boxes onto live
      // vars before translation.
      if (!c) return nullptr;

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
      return boolop::lor (boolop::land (c, t), 
                          boolop::land (mk<NEG>(c), e));
    }
    
    Expr exprFromCons(lincons_t lincons, theory_t *theory, ExprFactory &efac)
    {
      Expr lhs = exprFromTerm(theory->get_term(lincons), theory, efac);
      if (!lhs) return lhs; 
      
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
    
    // TODO: translation of Crab global singleton cells
    Expr exprFromIntVar (int v, ExprFactory &efac) {
      if (const Value* V = varMap->lookup(v)) {
        return bind::intConst (mkTerm (V, efac));
      }
      
      return nullptr; // this should not happen
    }
    
    Expr exprFromTerm (linterm_t term, theory_t *theory, ExprFactory &efac)
    {
      std::vector<Expr> coeffs (theory->term_size (term));
      
      for(size_t i = 0;i < coeffs.size (); i++) {
        Expr v = exprFromIntVar (theory->term_get_var (term,i), efac);
        if (!v) return v;
        
        coeffs[i] = lmult (exprFromIntCst (theory->term_get_coeff (term,i), 
                                           theory, efac), v);
      }
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

     LinConstToExpr m_t;

    public:

     DisIntervalToExpr (CrabLlvm* crab, const llvm::BasicBlock* bb, const ExprVector &live): 
         m_t (crab, bb, live) { }

     Expr toExpr (dis_interval_domain_t inv, ExprFactory &efac)
     {
       if (inv.is_top ())
         return mk<TRUE> (efac);
       
       if (inv.is_bottom ())
         return mk<FALSE> (efac);
       
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

       Expr e = m_t.exprFromIntVar (v, efac);
       if (!e) {
         // we could not translate the crab variable
         return mk<TRUE> (efac);
       }
       
       if (i.lb ().is_finite () && i.ub ().is_finite ()) {
         auto lb = *(i.lb ().number());
         auto ub = *(i.ub ().number());
         if (lb == ub) {
           return mk<EQ> (e, m_t.exprFromNum (lb, efac));
         } else {
           return mk<AND> (mk<GEQ> (e, m_t.exprFromNum (lb, efac)),
                           mk<LEQ> (e, m_t.exprFromNum (ub, efac)));
         }
       }
       
        if (i.lb ().is_finite ()) {
          auto lb = *(i.lb ().number());
          return mk<GEQ> (e, m_t.exprFromNum (lb, efac));
        }

        if (i.ub ().is_finite ()) {
          auto ub = *(i.ub ().number());
          return mk<LEQ> (e, m_t.exprFromNum (ub, efac));
        }
        // this should be unreachable
        return mk<TRUE> (efac);
     }    
   };

} // end namespace crab_llvm


namespace seahorn
{
  using namespace llvm;
  using namespace crab::cfg_impl;
  using namespace crab_llvm;
  using namespace expr;


  // Translate a range of Expr variables to Crab variables but only
  // those that can be mapped to llvm value.
  template<typename Range>
  static vector<varname_t> ExprVecToCrab (const Range & live, CrabLlvm* Crab) { 
    vector<varname_t> res;
    for (auto l: live) 
    {
      Expr u = bind::fname (bind::fname (l));
      if (isOpX<VALUE> (u)) 
      {
        const Value* v = getTerm <const Value*> (u);
        if (isa<GlobalVariable> (v)) continue;
        res.push_back (Crab->getVariableFactory ()[*v]);
      }
    }
    return res;
  }

  Expr CrabInvToExpr (const llvm::BasicBlock* B,
                      CrabLlvm* crab,
                      const ExprVector &live, 
                      EZ3& zctx,
                      ExprFactory &efac) 
  {
    Expr e = mk<TRUE> (efac);
    GenericAbsDomWrapperPtr abs = (*crab) [B];

    // TODO: note we don't project an arbitrary abstract domain onto
    // live variables because some abstract domains might not have a
    // precise implementation for it.

    #ifdef HAVE_LDD
    // --- translation of linear decision diagrams
    if (abs->getId () == GenericAbsDomWrapper::id_t::boxes) {
      boxes_domain_t boxes;
      getAbsDomWrappee (abs, boxes);        

      // Here we do project onto live variables before translation
      vector<varname_t> vars = ExprVecToCrab (live, crab);
      crab::domains::domain_traits<boxes_domain_t>::project (boxes, 
                                                             vars.begin (), 
                                                             vars.end ());

      LDDToExpr t = LDDToExpr (&boxes);
      e = t.toExpr (boxes.getLdd (), efac);
    }
    else if (abs->getId () == GenericAbsDomWrapper::id_t::arr_boxes) {
      arr_boxes_domain_t inv;
      getAbsDomWrappee (abs, inv);        
      boxes_domain_t boxes = inv.get_content_domain ();

      // Here we do project onto live variables before translation
      vector<varname_t> vars = ExprVecToCrab (live, crab);
      crab::domains::domain_traits<boxes_domain_t>::project (boxes, 
                                                             vars.begin (),
                                                             vars.end ());

      LDDToExpr t = LDDToExpr (&boxes);
      e = t.toExpr (boxes.getLdd (), efac);
    }
    else 
    #endif 
    { 
      // --- translation of disjunctive interval constraints
      if (abs->getId () == GenericAbsDomWrapper::id_t::dis_intv) {
        dis_interval_domain_t inv;
        getAbsDomWrappee (abs, inv);        
        DisIntervalToExpr t (crab, B, live);
        e = t.toExpr (inv, efac);
      }
      else if (abs->getId () == GenericAbsDomWrapper::id_t::arr_dis_intv) {
        arr_dis_interval_domain_t inv;
        getAbsDomWrappee (abs, inv);        
        DisIntervalToExpr t (crab, B, live);
        e = t.toExpr (inv.get_content_domain (), efac);
      }
      else {
        // --- translation to convex linear constraints
        LinConstToExpr t (crab, B, live);
        e = t.toExpr (abs->to_linear_constraints (), efac);
      }
    }
        
    if ((std::distance (live.begin (),live.end ()) == 0) && (!isOpX<FALSE> (e))) {
      e = mk<TRUE> (efac); 
    }

    return e;
  }

  bool LoadCrab::runOnModule (Module &M)
  {
    for (auto &F : M) {
      runOnFunction (F);
    }
    return false;
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

      Expr exp = CrabInvToExpr (&BB, &crab, live,
                                hm.getZContext (), hm.getExprFactory ());
                                
      Expr pred = hm.bbPredicate (BB);

      LOG ("crab", 
           errs () << "Loading invariant " << *bind::fname (pred);
           errs () << "("; for (auto v: live) errs () << *v << " ";
           errs () << ")  "  << *exp << "\n"; );
           

      db.addConstraint (bind::fapp (pred, live), exp);
      
    }
    return false;
  }
  
  
  void LoadCrab::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<HornifyModule> ();
    AU.addRequired<CrabLlvm> ();
  }

  // #ifdef HAVE_LDD
  // namespace expr_cnf {

  //    // Decides whether an expression represents a variable/constant
  //    class IsVar : public std::unary_function<Expr,bool>
  //    {
  //     private:
  //      /** list of exception expressions that are not treated as variables */
  //      ExprSet m_except;
  //     public:
  //      IsVar () {}
  //      IsVar (const ExprSet& except) : m_except (except) {}
  //      IsVar (const IsVar &o) : m_except (o.m_except) {}
  //      IsVar &operator= (IsVar o)
  //      {
  //        swap (*this, o);
  //     return *this;
  //      }
       
  //      /** add an exception expression */
  //      void exception (Expr e) { m_except.insert (e); }
       
  //      bool operator () (Expr e)
  //      {
  //        if (m_except.count (e) > 0) return false;
         
  //        // -- variant
  //        if (isOpX<VARIANT> (e))
  //          return true;
  //        // -- old-style constants
  //        if (bind::isBoolVar (e) || bind::isIntVar (e) || bind::isRealVar (e))
  //          return true;
  //        // -- new-style constants 
  //        if (bind::isBoolConst (e) || bind::isIntConst (e) || bind::isRealConst (e))
  //          return true;
  //        return false;
  //      }
  //    };
  
  //    // Return the set of variables in exp
  //    ExprSet getVars (Expr exp) {
  //      ExprSet s;
  //      filter (exp, IsVar (), std::inserter (s, s.begin ()));
  //      return s;
  //    }
  
  //    Expr mkRelation (ExprSet allVars, string fname, ExprFactory& efac) {
  //      ExprVector sorts;
  //      sorts.reserve (allVars.size () + 1);
  //      for (auto &v : allVars) {
  //        //assert (bind::isFapp (v));
  //        //assert (bind::domainSz (bind::fname (v)) == 0);
  //        sorts.push_back (bind::typeOf (v));
  //      }
       
  //      sorts.push_back (mk<BOOL_TY> (efac));
  //      Expr name = mkTerm (fname, efac);
  //      Expr decl = bind::fdecl (name, sorts);
  //      return decl;
  //    }

  //    // Convert e to CNF using a ZFixedPoint
  //    Expr cnf (EZ3 & zctx, ExprFactory &efac, Expr phi) {

  //      if (isOpX<FALSE> (phi)  || isOpX<TRUE> (phi))
  //        return phi;

  //      // Add two horn rules in fp
  //      // --- phi -> h
  //      // --- h and not phi -> false
  //      //
  //      // The solution is returned in cnf
       
  //      ZFixedPoint<EZ3> fp (zctx);
  //      ExprSet allVars = getVars (phi); 
  //      // -- register predicates
  //      Expr decl_h = mkRelation (allVars, "h",  efac);
  //      ExprSet emptyVars;
  //      Expr decl_p = mkRelation (emptyVars, "p",  efac);
  //      fp.registerRelation (decl_h);
  //      fp.registerRelation (decl_p);
  //      // -- add rules
  //      Expr h = bind::fapp (decl_h, allVars);
  //      Expr p = bind::fapp (decl_p, emptyVars);
  //      Expr r1 = mk<IMPL> (phi, h);
  //      fp.addRule (allVars, r1);
  //      Expr r2 = mk<IMPL> (mk<AND> (h, mk<NEG> (phi)), p);
  //      fp.addRule (allVars, r2);
  //      Expr r3 = mk<IMPL> (mk<FALSE> (efac), p);
  //      fp.addRule (emptyVars, r3);
       
  //      // -- add query
  //      fp.addQuery (h);
       
  //      LOG ("crab-cnf", errs () << "Content of fixedpoint: " << fp << "\n";);
  //      boost::tribool status = fp.query ();
  //      LOG ("crab-cnf", 
  //           if (status || !status) errs () << "result=" << fp.getAnswer () << "\n";);
  //      assert (status);
       
  //      Expr res = fp.getCex ();
  //      LOG ("crab-cnf", errs () << "Cnf=" << *res << "\n";);
       
  //      return res;
  //    }
  // } // end namespace
  // #endif 
  
} // end namespace seahorn
#endif
