#include "seahorn/Expr/ExprMemMap.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_ostream.h"
using namespace expr;

namespace expr {
namespace exprMemMap {

// supported expr ops that represent pointer
bool isMemArray(Expr exp) {
  return isOp<STORE>(exp) || isOp<CONST_ARRAY>(exp) || isOp<SET>(exp) ||
         isOp<CONST_FINITE_MAP>(exp);
}

// MemCell
MemCell::MemCell(Expr idx, Expr value, bool isRepeated)
    : m_pair(expr::numeric::convertToMpz(idx),
             expr::numeric::convertToMpz(value)),
      m_isRepeated(isRepeated) {}

bool MemCell::isSortable() const {
  return expr::numeric::isNumeric(m_pair.first);
}

/// \note assumes that the index is numeric
mpz_class MemCell::getIdxNum() const {
  assert(expr::numeric::isNumeric(m_pair.first));
  mpz_class returnValue = 0;
  expr::numeric::getNum(m_pair.first, returnValue);

  return returnValue;
}

/// converts indices to strings. Compares first by string size and then
/// lexicographically
bool MemCell::operator<(MemCell const &other) const {
  mpz_class num1 = 0;
  mpz_class num2 = 0;

  std::string s1 = "";
  std::string s2 = "";

  if (expr::numeric::getNum(m_pair.first, num1)) {
    s1 = num1.to_string(10);
  } else {
    std::stringstream ss;
    ss << m_pair.first;
    s1 = ss.str();
  }

  if (expr::numeric::getNum(other.m_pair.first, num2)) {
    s2 = num2.to_string(10);
  } else {
    std::stringstream ss;
    ss << other.m_pair.first;
    s2 = ss.str();
  }

  if (s1.size() == s2.size()) {
    return s1 < s2;
  }

  return s1.size() < s2.size();
}

// MemCellSet
void MemCellSet::insert(Expr idx, Expr value, bool repeated) {
  if (idx)
    MemCellSet::storeWidth(idx, m_widths.first);

  if (value)
    MemCellSet::storeWidth(value, m_widths.second);

  if (!bv::is_bvnum(value)) {
    m_isAligned = false;

  } else if (m_isAligned && m_widths.second != 0 &&
             expr::numeric::isNumeric(idx)) {
    // misaligned if the address is not divisble by the value's width

    mpz_class idxNum;
    expr::numeric::getNum(idx, idxNum);
    m_isAligned = (idxNum % m_widths.second) == 0;
  }

  m_set.emplace(idx, value, repeated);
}

void MemCellSet::setDefault(Expr defaultValue) {
  storeWidth(defaultValue, m_widths.second);
  m_defaultValue = defaultValue;
}

bool isWellFormedCond(Expr cond) {
  if (!isOp<EQ>(cond) && !isOp<NEQ>(cond))
    return false;
  using expr::numeric::isNumeric;
  if (isNumeric(cond->left()) == isNumeric(cond->right()))
    return false;

  return true;
}
// ITEVistor
VisitAction ITEVisitor::operator()(Expr exp) {
  if (!isOp<ITE>(exp))
    return VisitAction::doKids();

  Expr cond = exp->arg(0);
  Expr thenBranch = exp->arg(1);
  Expr elseBranch = exp->arg(2);

  if (!isWellFormedCond(cond)) {
    WARN << "Unhandled ITE condition (use `--log=cex.verbose` for more info)\n";
    LOG("cex.verbose", WARN << *exp);
    return VisitAction::doKids();
  }

  using expr::numeric::isNumeric;
  assert(isOp<EQ>(cond) || isOp<NEQ>(cond));
  // one side of the equals is numeric. The numeric side will be the key
  assert(isNumeric(cond->left()) != isNumeric(cond->right()));

  Expr key = isNumeric(cond->left()) ? cond->left() : cond->right();

  if (isOp<NEQ>(cond))
    std::swap(thenBranch, elseBranch);
  assert(!isOp<ITE>(thenBranch));

  m_cells->insert(key, thenBranch);

  // if there is not a nested ite
  if (!isOp<ITE>(elseBranch)) {
    m_cells->setDefault(elseBranch);
    return VisitAction::skipKids();
  }

  return VisitAction::doKids();
}

// array visitor
VisitAction ArrayVisitor::operator()(Expr exp) {

  if (isOp<STORE>(exp) || isOp<SET>(exp)) {

    Expr idx = exp->arg(1);
    Expr value = exp->arg(2);

    m_cells->insert(idx, value);

  } else if (isOp<CONST_ARRAY>(exp)) {
    m_cells->setDefault(exp->right());

  } else if (fmap::isFmapVal(exp)) {

    Expr keys = fmap::fmapValKeys(exp);
    Expr values = fmap::fmapValValues(exp);

    // maps every key in the finite set to its corresponding value
    for (auto bKey = keys->args_begin(), bVal = values->args_begin();
         bKey != keys->args_end() && bVal != values->args_end();
         bKey++, bVal++) {
      m_cells->insert(*bKey, *bVal);
    }
  }

  return VisitAction::doKids();
}

// ExprMemMap
bool ExprMemMap::populateCells(Expr exp) {
  if (isOp<ITE>(exp)) {
    m_visitor = std::make_unique<ITEVisitor>(&m_cells);
    dagVisit(*m_visitor, exp); // note: HD_ITE has its own cache

    m_visitor->doneVisiting();

  } else if (isMemArray(exp)) {
    m_visitor = std::make_unique<ArrayVisitor>(&m_cells);

    dagVisit(*m_visitor, exp);

    m_visitor->doneVisiting();
  } else {
    // if the expression is not a supported type, then this searches its
    // children for the first supported type
    ValidChildVisitor find;

    dagVisit(find, exp);

    if (find.m_found) {
      populateCells(find.m_exp);
    } else {
      m_visitor = std::make_unique<MemExprVisitor>(&m_cells);
      return false;
    }
  }
  return true;
}

} // namespace exprMemMap
} // namespace expr
