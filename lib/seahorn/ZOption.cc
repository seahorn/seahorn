#include "seahorn/Expr/Smt/Z3.hh"
#include "llvm/Support/CommandLine.h"

#include <string>

namespace seahorn {
struct ZTraceLogOpt {
  void operator=(const std::string &tag) const { Z3_enable_trace(tag.c_str()); }
};
ZTraceLogOpt ztrace;
}

static llvm::cl::opt<seahorn::ZTraceLogOpt, true, llvm::cl::parser<std::string>>
    TraceOption("ztrace", llvm::cl::desc("Enable z3 trace level"),
                llvm::cl::location(seahorn::ztrace),
                llvm::cl::value_desc("string"), llvm::cl::ValueRequired,
                llvm::cl::ZeroOrMore, llvm::cl::Hidden);
