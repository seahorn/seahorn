/// Pointer Expr -> Symbolic Memory Map
#pragma once
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprNumericUtils.hh"
#include "seahorn/Expr/ExprOpBool.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprVisitor.hh"

#include "seahorn/Support/SeaDebug.h"

namespace expr {
namespace exprMemMap {

bool isMemArray(Expr exp);

struct ValidChildVisitor {
  bool m_found = false;
  Expr m_exp = nullptr;

  bool isValidType(Expr exp) { return isOp<ITE>(exp) || isMemArray(exp); }

  VisitAction operator()(Expr exp) {
    if (!m_found && isValidType(exp)) {
      m_found = true;
      m_exp = exp;
    }
    return m_found ? VisitAction::skipKids() : VisitAction::doKids();
  }
};

/**
 * This is an individual cell in the memory map.
 * It stores an id: memory address
 * and an corresponding value: content stored at the address
 *
 * \note bvnums and UINT are stored as MPZ expressions
 */
class MemCell {
  std::pair<Expr, Expr> m_pair; // <addr, content>
  bool m_isRepeated = false;

public:
  MemCell(Expr idx, Expr value, bool isRepeated = false);

  bool isSortable() const;

  mpz_class getIdxNum() const;

  Expr getIdxExpr() const { return m_pair.first; }

  Expr getValueExpr() const { return m_pair.second; }

  bool isRepeated() const { return m_isRepeated; }

  /// based off of the index
  bool operator<(MemCell const &kv) const;

  bool operator==(MemCell const &other) const {
    return (m_pair == other.m_pair) && (m_isRepeated == other.m_isRepeated);
  }
};

using const_mc_iterator = std::set<MemCell>::const_iterator;
using const_mc_range = llvm::iterator_range<const_mc_iterator>;

/**
 * stores a set of MemCell objects; also contains functions to modify the cells
 */
class MemCellSet {

  std::set<MemCell> m_set;
  std::pair<unsigned, unsigned> m_widths;
  bool m_isAligned = true;

  Expr m_defaultValue;

  static void storeWidth(Expr exp, unsigned &widthDest) {
    unsigned bits = 0;
    if (!bv::isBvNum(exp, bits)) { // note: isBvNum stores the width
      mpz_class num = 0;

      if (expr::numeric::getNum(exp, num)) {
        bits = num.sizeInBase(2);
      }
    }

    unsigned bytes = std::ceil((float)bits / 8);

    widthDest = std::max(bytes, widthDest);
  }

public:
  MemCellSet() : m_widths(0, 0) {}

  void insert(Expr idx, Expr value, bool repeated = false);

  void setDefault(Expr defaultValue);

  Expr getDefault() const { return m_defaultValue; }

  bool isAligned() const { return m_isAligned; }

  const_mc_iterator cbegin() const { return m_set.cbegin(); }

  const_mc_iterator cend() const { return m_set.cend(); }

  size_t getIdWidth() const { return m_widths.first; }

  size_t getContentWidth() const { return m_widths.second; }

  size_t size() const { return m_set.size(); }
};

// Expr visitors; override operator()
class MemExprVisitor {

protected:
  MemCellSet *m_cells;
  bool m_visiting_done = false;

public:
  MemExprVisitor(MemCellSet *cells) : m_cells(cells) {}
  virtual ~MemExprVisitor() = default;

  virtual VisitAction operator()(Expr exp){};

  void doneVisiting() { m_visiting_done = true; }
};

class ITEVisitor : public MemExprVisitor {
public:
  ITEVisitor(MemCellSet *cells) : MemExprVisitor(cells) {}
  VisitAction operator()(Expr exp) override;
};

class ArrayVisitor : public MemExprVisitor {
public:
  ArrayVisitor(MemCellSet *cells) : MemExprVisitor(cells) {}

  VisitAction operator()(Expr exp) override;
};

class ExprMemMap {
  bool is_valid = true;
  std::unique_ptr<MemExprVisitor> m_visitor;
  /* extra actions needed after populating default value and special values
     with ID
  */

  /* populate m_cells using input Expr using m_visitor */
  bool populateCells(Expr e);

protected:
  MemCellSet m_cells;
  Expr m_expr;

public:
  ExprMemMap(Expr e) : m_expr(e) { is_valid = populateCells(e); }
  ~ExprMemMap() = default;

  bool isValid() const { return is_valid; }

  // proxy functions for m_cells properties
  Expr getDefault() const { return m_cells.getDefault(); }

  size_t getContentWidth() const { return m_cells.getContentWidth(); }

  const_mc_iterator cbegin() const { return m_cells.cbegin(); }

  const_mc_iterator cend() const { return m_cells.cend(); }

  Expr getRawExpr() const { return m_expr; }
};
} // namespace exprMemMap
} // namespace expr
