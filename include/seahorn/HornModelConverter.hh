#ifndef HORNMODEL_CONVERTER__HH_
#define HORNMODEL_CONVERTER__HH_

#include "seahorn/HornClauseDB.hh"
#include "seahorn/HornifyModule.hh"
#include "seahorn/HornDbModel.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"

namespace seahorn
{
  class HornModelConverter
  {
  public:
    // converts a model from one database to another. returns false on failure.
    virtual bool convert (HornDbModel &in, HornDbModel &out) = 0;
    virtual ~HornModelConverter() {}
  };
}

#endif
