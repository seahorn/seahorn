#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "llvm/Support/raw_ostream.h"
#include "seahorn/config.h"

namespace seahorn
{
  using namespace llvm;

  /// Loads Ikos invariants into  a Horn Solver
  class LoadIkos: public llvm::ModulePass
  {
  public:
    static char ID;
    
    LoadIkos () : ModulePass(ID) {}
    virtual ~LoadIkos () {}
    
    virtual bool runOnModule (Module &M);
    virtual bool runOnFunction (Function &F);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "LoadIkos";}
  };
  
  char LoadIkos::ID = 0;
  Pass* createLoadIkosPass () {return new LoadIkos ();}

} // end namespace seahorn

#ifndef HAVE_IKOS_LLVM
// dummy implementation when Ikos is not compiled in
namespace seahorn
{
  void LoadIkos::getAnalysisUsage (AnalysisUsage &AU) const
  {AU.setPreservesAll ();}

  bool LoadIkos::runOnModule (Module &M)
  {
    errs () << "WARNING: Not loading invariants. Compiled without Ikos support.\n";
    return false;
  }
  bool LoadIkos::runOnFunction (Function &F) {return false;}
}
#else
  // real implementation starts here 
#include "ufo/Expr.hpp"
#include "ufo/ExprLlvm.hpp"

#include <ikos_llvm/CfgBuilder.hh>
#include <ikos_llvm/LlvmIkos.hh>
#include <ikos_llvm/Support/bignums.hh>

#include "seahorn/HornifyModule.hh"

#include "llvm/Support/CommandLine.h"

namespace llvm
{
   template <typename Number, typename VariableName>
   llvm::raw_ostream& operator<< (llvm::raw_ostream& o, 
                                  cfg_impl::z_lin_cst_t cst)
   {
     std::ostringstream s;
     s << cst;
     o << s.str ();
     return o;
   }

   inline llvm::raw_ostream& operator<< (llvm::raw_ostream& o, 
                                         cfg_impl::z_lin_cst_sys_t csts)
   {
     std::ostringstream s;
     s << csts;
     o << s.str ();
     return o;
   }

} // end namespace

namespace seahorn
{
  namespace ikos_smt 
  {
    // TODO: marshal expr::Expr to ikos::linear_constraints

    using namespace llvm;
    using namespace expr;
    using namespace cfg_impl;

    struct FailUnMarshal
    {
      static Expr unmarshal (const z_lin_cst_t &cst, ExprFactory &efac)
      { 
        llvm::errs () << "Cannot unmarshal: " << cst << "\n";
        assert (0); exit (1); 
      }
    };
      
    template <typename U>
    struct BasicExprUnMarshal
    {
      // Ikos does not distinguish between bools and the rest of
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
      
      Expr unmarshal_num( ikos::z_number n, ExprFactory &efac)
      {
        std::string snum = llvm_ikos::toStr (n);
        const mpz_class mpz (snum);
        return mkTerm (mpz, efac);
      }
       
      Expr unmarshal_int_var( varname_t v, ExprFactory &efac)
      {
        assert (v.get () && "Cannot have shadow vars");
        Expr e = mkTerm<const Value*>(*(v.get()), efac);
        return bind::intConst (e);
      }
       
      Expr unmarshal (z_lin_cst_t cst, ExprFactory &efac)
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
        Expr ee = unmarshal_num ( ikos::z_number ("0"), efac);
        for (auto t : e)
        {
          ikos::z_number n  = t.first;
          varname_t v = t.second.name();
          if (n == 0) continue;
          else if (n == 1) 
            ee = mk<PLUS> (ee, unmarshal_int_var (v, efac));
          else if (n == -1) 
            ee = mk<MINUS> (ee, unmarshal_int_var (v, efac));
          else
            ee = mk<PLUS> (ee, mk<MULT> ( unmarshal_num (n, efac), 
                                          unmarshal_int_var (v, efac)));
        }

        ikos::z_number c = -cst.expression().constant();
        Expr cc = unmarshal_num (c, efac);
        if (cst.is_inequality ())
          return mk<LEQ> (ee, cc);
        else if (cst.is_equality ())
          return mk<EQ> (ee, cc);        
        else 
          return mk<NEQ> (ee, cc);
        
      }
       
      Expr unmarshal (z_lin_cst_sys_t csts, ExprFactory &efac)
      {
        Expr e = mk<TRUE> (efac);

        // integers
        for (auto cst: csts)
        { e = boolop::land (e, unmarshal (cst, efac)); } 

        // booleans 
        for (auto p: bool_map)
        {
          auto b = p.second;
          if (!b.isUnknown ()) { e = boolop::land (e, b.toExpr (efac)); }
        }

        return e;
      }
    };

  } // end namespace ikos_smt

} // end namespace seahorn


namespace seahorn
{
  using namespace llvm;
  using namespace cfg_impl;
  
  
  bool LoadIkos::runOnModule (Module &M)
  {
    for (auto &F : M) runOnFunction (F);
    return true;
  }
  
  expr::Expr Convert (llvm_ikos::LlvmIkos &ikos,
                      const llvm::BasicBlock *BB, 
                      const expr::ExprVector &live, 
                      expr::ExprFactory &efac) 
  {
    z_lin_cst_sys_t csts = ikos [BB];
    ikos_smt::BasicExprUnMarshal < ikos_smt::FailUnMarshal > c;
    expr::Expr inv = c.unmarshal (csts, efac);

    if ( (std::distance (live.begin (), live.end ()) == 0) && 
         (!expr::isOpX<expr::FALSE> (inv)))
      return expr::mk<expr::TRUE> (efac); 
    else 
      return inv;
  }

  bool LoadIkos::runOnFunction (Function &F)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    llvm_ikos::LlvmIkos &ikos = getAnalysis<llvm_ikos::LlvmIkos> ();
    
    auto &db = hm.getHornClauseDB ();
    
    for (auto &BB : F)
    {
      // skip all basic blocks that HornifyModule does not know
      if (! hm.hasBbPredicate (BB)) continue;
      
      const ExprVector &live = hm.live (BB);
      
      Expr pred = hm.bbPredicate (BB);
      Expr inv = Convert (ikos, &BB, live, hm.getExprFactory ());

      LOG ("ikos", 
           errs () << "Loading invariant " << *bind::fname (pred);
           errs () << "("; for (auto v: live) errs () << *v << " ";
           errs () << ")  "  << *inv << "\n"; );
           

      db.addConstraint (bind::fapp (pred, live), inv);
      
    }
    return true;
  }
  
  
  void LoadIkos::getAnalysisUsage (AnalysisUsage &AU) const
  {
    AU.setPreservesAll ();
    AU.addRequired<HornifyModule> ();
    AU.addRequired<llvm_ikos::LlvmIkos> ();
  }
  
}
#endif
