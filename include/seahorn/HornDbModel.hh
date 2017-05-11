#ifndef HORNDBMODEL__HH_
#define HORNDBMODEL__HH_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/Z3n.hpp"
#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
  class HornDbModel
  {
  public:
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

  void initDBModelFromFile(HornDbModel &dbModel, HornClauseDB &db, EZ3& z3, const char *fname);
}

#endif
