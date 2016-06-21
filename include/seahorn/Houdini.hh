#ifndef HOUDINI__HH_
#define HOUDINI__HH_

#include "llvm/Pass.h"
#include "llvm/IR/Module.h"
#include "seahorn/HornClauseDB.hh"

#include "ufo/Expr.hpp"

namespace seahorn
{
  using namespace llvm;

  class Houdini : public llvm::ModulePass
  {
  public:
    static char ID;
    
    //std::map<Expr, int> bvar_map;

    Houdini() : ModulePass(ID) {}
    virtual ~Houdini() {}

    virtual bool runOnModule (Module &M);
    virtual void getAnalysisUsage (AnalysisUsage &AU) const;
    virtual const char* getPassName () const {return "Houdini";}

    void printDB (const HornClauseDB &db);
    void printHello ();
    Expr guessCandidate(Expr pred);
    int testGuessCandidate(Expr pred);
    bool validateRule(Expr cand_app);
    void workListAlgo(HornClauseDB &db);

    template<typename OutputIterator>
    void get_all_bvars (Expr e, OutputIterator out);
    struct IsBVar : public std::unary_function<Expr, bool>
    {
      //Expr m_expr;
      //IsBVar (Expr expr) : m_expr(expr) {}
      IsBVar () {}
      bool operator() (Expr e)
      {return bind::isBVar (e);}
    };
    template<typename OutputIterator>
    void get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out);
    struct IsPredApp : public std::unary_function<Expr, bool>
    {
      HornClauseDB &m_db;
      IsPredApp (HornClauseDB &db) : m_db (db) {}

      bool operator() (Expr e)
      {return bind::isFapp (e) && m_db.hasRelation (bind::fname(e));}
    };
    void getUseRuleSet(HornClauseDB &db);
  };

  template<typename OutputIterator>
  void Houdini::get_all_bvars (Expr e, OutputIterator out)
  {filter (e, Houdini::IsBVar(), out);}

  template<typename OutputIterator>
  void Houdini::get_all_pred_apps (Expr e, HornClauseDB &db, OutputIterator out)
  {filter (e, Houdini::IsPredApp(db), out);}
}

#endif /* HOUDNINI__HH_ */
