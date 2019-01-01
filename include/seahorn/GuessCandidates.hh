#ifndef GUESS_CANDIDATES__HH_
#define GUESS_CANDIDATES__HH_

#include "seahorn/HornifyModule.hh"

#include "ufo/Expr.hpp"
#include "ufo/Smt/EZ3.hh"
#include <fstream>
#include <iostream>
#include <boost/tokenizer.hpp>

namespace seahorn
{
  //Simple templates
  ExprVector relToCand(Expr pred);
  //Load templates from file
  ExprVector applyTemplatesFromExperimentFile(Expr fdecl,
                                              const std::string &filepath);
  void parseLemmasFromExpFile(Expr bvar, ExprVector& lemmas,
                              const std::string &filepath);
}

#endif
