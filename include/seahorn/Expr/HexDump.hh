#pragma once
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprMemMap.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "llvm/Support/Format.h"

// pretty printer for ExprMemMap
namespace expr {
namespace hexDump {
using namespace exprMemMap;
// helper functions
void getValueStr(Expr value, unsigned desiredNumBytes, bool includeAscii,
                 llvm::raw_string_ostream &stream);

void getIdxStr(Expr value, unsigned desiredNumBytes,
               llvm::raw_string_ostream &stream);

void getCellStr(const MemCell &cell, llvm::raw_string_ostream &stream,
                size_t idWidth, size_t contentWidth, bool includeAscii,
                bool isDefault = false);

class HexDump : public ExprMemMap {
  void fillInGaps();

public:
  HexDump(Expr exp) : ExprMemMap(exp) {
    if (isValid())
      fillInGaps();
  }

  template <typename T> void print(T &OS, bool includeAscii = true) const;

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                       HexDump const &hd);

  friend std::ostream &operator<<(std::ostream &OS, HexDump const &hd);
};

/**
 * Hex dump specific for MK_STRUCT
 *
 * Creates a new (separate) HexDump instance for every child of the struct
 */
class StructHexDump {
  Expr m_exp;
  std::vector<std::unique_ptr<HexDump>> hexDumps;

public:
  StructHexDump(Expr exp);

  std::vector<const_mc_range> getRanges() const;

  template <typename T> void print(T &OS, bool includeAscii = true) const;

  friend llvm::raw_ostream &operator<<(llvm::raw_ostream &OS,
                                       StructHexDump const &hd);

  friend std::ostream &operator<<(std::ostream &OS, StructHexDump const &hd);
};

/**
 * modified from Adrian Schneider from
 * https://stackoverflow.com/questions/36802354/print-binary-tree-in-a-pretty-way-using-c
 */
inline void printIteTreeHelper(std::string prefix, std::string nodeName,
                               Expr exp, bool isBottom) {
  llvm::errs() << prefix;

  llvm::errs() << (isBottom ? "└──" : "├──") << nodeName << " ";

  if (isOpX<ITE>(exp)) {

    llvm::errs() << "\n";

    printIteTreeHelper(prefix + (isBottom ? "    " : "│   "), "I", exp->arg(0),
                       false);
    printIteTreeHelper(prefix + (isBottom ? "    " : "│   "), "T", exp->arg(1),
                       false);
    printIteTreeHelper(prefix + (isBottom ? "    " : "│   "), "E", exp->arg(2),
                       true);
  } else {
    llvm::errs() << *exp << "\n";
  }
}

inline void printIteTree(Expr exp) { printIteTreeHelper("", "", exp, true); }

} // namespace hexDump
} // namespace expr
