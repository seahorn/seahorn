#ifndef HORNDBMODEL__HH_
#define HORNDBMODEL__HH_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
  class HornDbModel
  {
  private:
    ExprMap m_defs;
  public:
    HornDbModel() {}
    void addDef(Expr fapp, Expr lemma);
    Expr getDef(Expr fapp);
    bool hasDef (Expr fdecl);
    virtual ~HornDbModel() {}
  };

  /// Extract HornDbModel of a given horn db from a ZFixedPoint. 
  void initDBModelFromFP(HornDbModel &dbModel, HornClauseDB &db, ZFixedPoint<EZ3> &fp);
}

#endif
