#ifndef __HORNIFY_MODULE_HH_
#define __HORNIFY_MODULE_HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include "seahorn/UfoOpSem.hh"
#include "seahorn/ClpOpSem.hh"

#include "boost/smart_ptr/scoped_ptr.hpp"

#include "seahorn/LiveSymbols.hh"

#include "seahorn/HornClauseDB.hh"
#include "seahorn/Analysis/CutPointGraph.hh"
namespace seahorn
{
  using namespace expr;
  using namespace llvm;
  using namespace ufo;

  class HornifyModule : public llvm::ModulePass
  {
    typedef llvm::DenseMap<const Function*, LiveSymbols> LiveSymbolsMap;
    typedef llvm::DenseMap<const BasicBlock*, Expr> PredDeclMap;

  protected:

    ExprFactory m_efac;
    EZ3 m_zctx;
    HornClauseDB m_db;

    const DataLayout *m_td;
    const CanFail *m_canFail;
    boost::scoped_ptr<LegacyOperationalSemantics> m_sem;

    LiveSymbolsMap m_ls;
    PredDeclMap m_bbPreds;

  public:
    static char ID;
    HornifyModule ();
    virtual ~HornifyModule () {}
    ExprFactory& getExprFactory () {return m_efac;}
    EZ3 &getZContext () {return m_zctx;}
    HornClauseDB& getHornClauseDB () {return m_db;}
    virtual bool runOnModule (Module &M);
    virtual bool runOnFunction (Function &F);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual StringRef getPassName () const {return "HornifyModule";}

    /// --- live symbols for a function
    const LiveSymbols& getLiveSybols (const Function &F) const;
    /// -- live symbols for a basic block
    const ExprVector &live (const BasicBlock &bb) const
    {
      return getLiveSybols (*bb.getParent ()).live (&bb);
    }
    /// --- live symbols for a basic block
    const ExprVector &live (const BasicBlock *bb) const
    {assert (bb != NULL); return live (*bb);}
    bool hasBbPredicate (const BasicBlock &BB) const
    {return m_bbPreds.count (&BB);}
    /// -- predicate declaration for the given basic block
    const Expr bbPredicate (const BasicBlock &bb);
    /// --- BasicBlock corresponding to the predicate
    const BasicBlock &predicateBb (Expr pred) const;
    /// --- Checks whether the expression is a BasicBlock predicate
    bool isBbPredicate (Expr pred) const;
    /// -- summary predicate for a function
    const Expr summaryPredicate (const Function &F)
    {
      return m_sem->hasFunctionInfo (F) ?
        m_sem->getFunctionInfo (F).sumPred : Expr(0);
    }
    /// -- symbolic execution engine
    LegacyOperationalSemantics &symExec () {return *m_sem;}

    CutPointGraph &getCpg (Function &F)
    {return getAnalysis<CutPointGraph> (F);}

  };
}


#endif
