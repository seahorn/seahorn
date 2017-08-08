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

#include "crab_llvm/CrabLlvm.hh"
#include "crab_llvm/HeapAbstraction.hh"
#include "crab_llvm/wrapper_domain.hh"

namespace crab_llvm {
  
  using namespace llvm;
  using namespace expr;
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

    typedef DenseMap<const Value*, BoolCst> bool_map_t;
    bool_map_t bool_map;
    
   public:

    LinConstToExpr (CrabLlvm* crab,
		    // needed by crab-llvm memory analysis
		    const llvm::BasicBlock* bb,
		    const ExprVector &live): 
        m_crab (crab), m_bb (bb), m_live (live) { 

      for (auto v: m_live) 
      {
        Expr u = bind::fname (bind::fname (v));
        if (isOpX<VALUE> (u)) 
          m_live_values.insert (getTerm <const Value*> (u));
      }

    }      
    
    
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

      if (const Value* Gv = m_crab->getHeapAbstraction().
	  getRegion(*(const_cast <Function*> (m_bb->getParent ())), 
		    const_cast<Value*> (V)).getSingleton ()) {
	
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
        else { bool_map.insert (std::make_pair (v, b2)); } 
        
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
  
  // Conversion from boxes domain to Expr
  class BoxesToExpr
  {
    typedef typename boxes_domain_t::varname_t varname_t;
    typedef typename boxes_domain_t::number_t number_t;
    LinConstToExpr m_t;
    
  public:
    
    BoxesToExpr (CrabLlvm* crab,
		 const llvm::BasicBlock* bb,
		 const ExprVector &live): 
      m_t (crab, bb, live) { }
    
    Expr toExpr (boxes_domain_t inv, ExprFactory &efac) {
      auto csts = inv.to_disjunctive_linear_constraint_system ();
      if (csts.is_false ())
	return mk<FALSE>(efac);
      else if (csts.size () == 0)
	 return mk<TRUE>(efac);
      else {
	assert (csts.size () > 0);
	Expr e = mk<FALSE> (efac);
	for (auto cst : csts) {
	  e = boolop::lor (e, m_t.toExpr(cst, efac));
	}
	return e;
      }
    }
  };
  
  // Conversion from domain of disjunctive intervals to Expr
  class DisIntervalToExpr
  {
    typedef typename dis_interval_domain_t::interval_t interval_t;
    typedef typename dis_interval_domain_t::varname_t varname_t;
    typedef typename dis_interval_domain_t::number_t number_t;
    
    LinConstToExpr m_t;
    
  public:
    
    DisIntervalToExpr (CrabLlvm* crab,
		       const llvm::BasicBlock* bb,
		       const ExprVector &live): 
      m_t (crab, bb, live) { }
    
    Expr toExpr (dis_interval_domain_t inv, ExprFactory &efac) {
      if (inv.is_top ())
	return mk<TRUE> (efac);
      
      if (inv.is_bottom ())
	return mk<FALSE> (efac);
      
       Expr e = mk<TRUE> (efac);
       // bit ugly: dis_interval_domain_t is wrapped into array smashing.
       // That's why we need to call first get_contain_domain().
       auto &dis_intvs = inv.get_content_domain().second(); 
       for (auto p: boost::make_iterator_range (dis_intvs.begin (), dis_intvs.end ())) {
	 Expr d = mk<FALSE> (efac);
	 for (auto i: boost::make_iterator_range (p.second.begin (),
						  p.second.end ())) {
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
  using namespace crab_llvm;
  using namespace expr;
  
  // Translate a range of Expr variables to Crab variables but only
  // those that can be mapped to llvm value.
  template<typename Range>
  static std::vector<varname_t> ExprVecToCrab (const Range & live, CrabLlvm* Crab) { 
    std::vector<varname_t> res;
    for (auto l: live) 
    {
      Expr u = bind::fname (bind::fname (l));
      if (isOpX<VALUE> (u)) 
      {
        const Value* v = getTerm <const Value*> (u);
        if (isa<GlobalVariable> (v)) continue;
        res.push_back (Crab->getVariableFactory()[v]);
      }
    }
    return res;
  }

  Expr CrabInvToExpr (const llvm::BasicBlock* B,
                      CrabLlvm* crab,
                      const ExprVector &live, 
                      EZ3& zctx,
                      ExprFactory &efac) { 
    Expr e = mk<TRUE> (efac);
    GenericAbsDomWrapperPtr abs = (*crab) [B];

    // TODO: note we don't project an arbitrary abstract domain onto
    // live variables because some abstract domains might not have a
    // precise implementation for it.

    
    if (abs->getId () == GenericAbsDomWrapper::id_t::boxes) {
      // --- special translation for boxes
      boxes_domain_t boxes;
      getAbsDomWrappee (abs, boxes);        

      // Here we do project onto live variables before translation
      std::vector<varname_t> vars = ExprVecToCrab (live, crab);
      crab::domains::domain_traits<boxes_domain_t>::project (boxes, 
                                                             vars.begin (), 
                                                             vars.end ());
      BoxesToExpr t (crab, B, live);      
      e = t.toExpr (boxes, efac);
    } else if (abs->getId () == GenericAbsDomWrapper::id_t::dis_intv) {
      // --- special translation of disjunctive interval constraints
      dis_interval_domain_t inv;
      getAbsDomWrappee (abs, inv);        
      DisIntervalToExpr t (crab, B, live);
      e = t.toExpr (inv, efac);
    } else {
      // --- rest of domains translated to convex linear constraints
      LinConstToExpr t (crab, B, live);
      e = t.toExpr (abs->to_linear_constraints (), efac);
    }
        
    if ((std::distance (live.begin (),live.end ()) == 0) && (!isOpX<FALSE> (e))) {
      e = mk<TRUE> (efac); 
    }

    return e;
  }

  bool LoadCrab::runOnModule (Module &M) {
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
  
} // end namespace seahorn
#endif
