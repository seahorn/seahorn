#include "llvm/Support/CommandLine.h"

#include "avy/AvyDebug.h"

#include <string>
#include <set>

#ifndef NAVYLOG
using namespace avy;

bool avy::AvyLogFlag = false;
std::set<std::string> avy::AvyLog;

void avy::AvyEnableLog (std::string x) 
{
  if (x.empty ()) return;
  AvyLogFlag = true;
  AvyLog.insert (x); 
}

namespace avy
{
  struct LogOpt
  { void operator= (const std::string &tag) const { avy::AvyEnableLog (tag); } };
  
  LogOpt loc;
}



static llvm::cl::opt<avy::LogOpt, true, llvm::cl::parser<std::string> > 
LogClOption ("log",
             llvm::cl::desc ("Enable specified log level"),
             llvm::cl::location (avy::loc),
             llvm::cl::value_desc ("string"),
             llvm::cl::ValueRequired, llvm::cl::ZeroOrMore);

#else
#endif

