#include "llvm/Support/CommandLine.h"

#include "seahorn/Support/SeaDebug.h"

#include <set>
#include <string>

#ifndef NSEALOG

namespace sea_dsa {
extern void SeaDsaEnableLog(std::string x);
}

using namespace seahorn;

bool seahorn::SeaLogFlag = false;
std::set<std::string> seahorn::SeaLog;

void seahorn::SeaEnableLog(std::string x) {
  if (x.empty())
    return;
  SeaLogFlag = true;
  SeaLog.insert(x);

  // Enable logging in sea_dsa in case it uses the same tags.
  sea_dsa::SeaDsaEnableLog(x);
}

namespace seahorn {
struct LogOpt {
  void operator=(const std::string &tag) const { seahorn::SeaEnableLog(tag); }
};

LogOpt loc;
}

static llvm::cl::opt<seahorn::LogOpt, true, llvm::cl::parser<std::string>>
    LogClOption("log", llvm::cl::desc("Enable specified log level"),
                llvm::cl::location(seahorn::loc), llvm::cl::value_desc("string"),
                llvm::cl::ValueRequired, llvm::cl::ZeroOrMore);

#else
#endif
