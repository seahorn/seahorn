#pragma once
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"

namespace expr {

namespace hexDump {
/**
 * This is an individual cell in the hex dump. It stores a key and its
 * corresponding value
 *
 * \note bvnums and UINT are stored as MPZ expressions
 */
class KeyValue {
  std::pair<Expr, Expr> m_pair; // <key, value>
  bool m_isRepeated = false;

public:
  KeyValue(Expr idx, Expr value, bool isRepeated = false);

  bool isSortable() const;

  template <typename T>
  void
  print(T &OS,
        std::pair<unsigned, unsigned> widths = std::pair<unsigned, unsigned>(0,
                                                                             0),
        bool includeAscii = true) const;

  mpz_class getIdxNum() const;

  Expr getIdxExpr() const { return m_pair.first; }

  Expr getValueExpr() const { return m_pair.second; }

  bool isRepeated() const { return m_isRepeated; }

  /// based off of the index
  bool operator<(KeyValue const &kv) const;

  bool operator==(KeyValue const &kv) const {
    return (m_pair == kv.m_pair) && (m_isRepeated == kv.m_isRepeated);
  }

  /// prints with ascii and no set width
  friend std::ostream &operator<<(std::ostream &OS, KeyValue const &kv);
};

using const_hd_iterator = std::set<KeyValue>::const_iterator;
using const_hd_range = llvm::iterator_range<const_hd_iterator>;

/**
 * Supports nested ITE expressions, arrays (STORE) and finite
 * maps (SET)
 *
 * Supported format of ITE expressions (ite(condition, then, else)):
 *    condition: EQ or NEQ. One of the the children should be numeric (bvnum,
 *    mpz_class, unsigned) - this is the key
 *
 *    then: the value if the condition is an EQ expression. Can be a nested ITE
 *    if the condition is a NEQ expression
 *
 *    else: the value if the condition is a NEQ expression. Can be a nested ITE
 *    if the condition is an EQ expression
 *
 * If the given expression is not one of the supported expressions (ITE, STORE,
 * SET) above, it will search its children for the first supported expression
 * and use that.
 *
 * Widths:
 *    bvnums: uses the width of the bvnum
 *
 *    UINT/MPZ : uses the max width of all the numbers
 *
 * Alignment:
 *    bvnums: assumes the addresses are aligned based on the width of the value
 *      unless it finds an index/key that is misaligned (not divisible by the
 *      width (in bytes))
 *
 *    uint/mpz: assumes its not aligned

 */
class HexDump {
  class Impl;
  Impl *m_impl;

public:
  HexDump(Expr exp);
  ~HexDump();

  const_hd_iterator cbegin() const;
  const_hd_iterator cend() const;

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
  class StructImpl;
  StructImpl *m_impl;

public:
  StructHexDump(Expr exp);
  ~StructHexDump();

  std::vector<const_hd_range> getRanges() const;

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
