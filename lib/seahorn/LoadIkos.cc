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
                                  cfg_impl::ZLinearConstraint cst)
   {
     std::ostringstream s;
     s << cst;
     o << s.str ();
     return o;
   }

   inline llvm::raw_ostream& operator<< (llvm::raw_ostream& o, 
                                         cfg_impl::ZLinearConstraintSystem csts)
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

    using namespace llvm;
    using namespace expr;

    using namespace cfg_impl;

    // TODO: marshal expr::Expr to ikos::linear_constraints
    struct FailUnMarshal
    {
      static Expr unmarshal (const ZLinearConstraint &cst, ExprFactory &efac)
      { 
        llvm::errs () << "Cannot unmarshal: " << cst << "\n";
        assert (0); exit (1); 
      }
    };
   
   
    template <typename U>
    struct BasicExprUnMarshal
    {
      static Expr unmarshal_num( ikos::z_number n, ExprFactory &efac)
      {
        std::string snum = llvm_ikos::toStr (n);
        const mpz_class mpz (snum);
        return mkTerm (mpz, efac);
      }
       
      static Expr unmarshal_var( varname_t v, ExprFactory &efac)
      {
        Expr e = mkTerm<const Value*>(v.get(), efac);
        return bind::intConst (e);
      }
       
      static Expr unmarshal (ZLinearConstraint cst, ExprFactory &efac)
      {
        if      (cst.is_tautology ())     return mk<TRUE> (efac);
        else if (cst.is_contradiction ()) return mk<FALSE> (efac);
        else
        {
          ZLinearExpression e = cst.expression() - cst.expression().constant();
          Expr ee = unmarshal_num ( ikos::z_number ("0"), efac);
          for (auto t : e)
          {
            ikos::z_number n  = t.first;
            varname_t v = t.second.name();
            if (n == 0) continue;
            else if (n == 1) 
              ee = mk<PLUS> (ee, unmarshal_var (v, efac));
            else if (n == -1) 
              ee = mk<MINUS> (ee, unmarshal_var (v, efac));
            else
              ee = mk<PLUS> (ee, mk<MULT> ( unmarshal_num (n, efac), unmarshal_var (v, efac)));
          }
          ikos::z_number c = -cst.expression().constant();
          Expr cc = unmarshal_num (c, efac);
          if (cst.is_inequality ())
            return mk<LEQ> (ee, cc);
          else if (cst.is_equality ())
            return mk<EQ> (ee, cc);        
          else return mk<NEQ> (ee, cc);
        }
        return U::unmarshal (cst, efac);
      }
       
      static Expr unmarshal (ZLinearConstraintSystem csts, ExprFactory &efac)
      {
        if (csts.size () == 0) return mk<TRUE> (efac);
         
        ZLinearConstraintSystem::iterator it = csts.begin();
        Expr e = unmarshal (*it, efac);
        ++it;
        for( ; it != csts.end(); ++it)
          e = mk<AND> (e, unmarshal (*it, efac));
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
                      const expr::ExprVector &live, expr::ExprFactory &efac) 
  {
    ZLinearConstraintSystem csts = ikos [BB];
    ikos_smt::BasicExprUnMarshal < ikos_smt::FailUnMarshal > c;
    expr::Expr inv = c.unmarshal (csts, efac);
    if ( (live.size () == 0) && (!expr::isOpX<expr::FALSE> (inv)))
      return expr::mk<expr::TRUE> (efac);
    else
      return inv;
  }

  bool LoadIkos::runOnFunction (Function &F)
  {
    HornifyModule &hm = getAnalysis<HornifyModule> ();
    llvm_ikos::LlvmIkos &ikos = getAnalysis<llvm_ikos::LlvmIkos> ();
    
    //auto &fp = hm.getZFixedPoint ();
    auto &db = hm.getHornClauseDB ();
    
    for (auto &BB : F)
    {
      // skip all basic blocks that HornifyModule does not know
      if (! hm.hasBbPredicate (BB)) continue;
      
      const ExprVector &live = hm.live (BB);
      
      Expr pred = hm.bbPredicate (BB);
      Expr inv = Convert (ikos, &BB, live, hm.getExprFactory ());
      LOG ("ikos", errs () << "Loading invariant at " << *bind::fname (pred) 
           << ":"  << *inv << "\n";);
      db.addCover (bind::fapp (pred, live), inv);
      
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
