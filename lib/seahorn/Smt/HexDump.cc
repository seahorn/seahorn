#include "seahorn/Expr/HexDump.hh"
#include "seahorn/Expr/ExprLlvm.hh"
#include "seahorn/Expr/ExprOpCore.hh"
#include "seahorn/Expr/ExprOpFiniteMap.hh"
#include "seahorn/Expr/ExprVisitor.hh"

#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"
#include "llvm/Support/Format.h"
#include "llvm/Support/raw_ostream.h"
using namespace expr;

namespace kvUtils {

/// \param[out] num the number/value of the expression
/// \return true if the expression was numeric
bool getNum(Expr exp, mpz_class &num) {
  if (isOp<MPZ>(exp)) {
    num = getTerm<mpz_class>(exp);

    return true;
  } else if (isOp<UINT>(exp)) {
    unsigned unsignedNum = getTerm<unsigned>(exp);
    num = mpz_class(unsignedNum);

    return true;
  }

  return false;
}

bool isNumeric(Expr exp) {
  mpz_class placeholder;
  return getNum(exp, placeholder);
}

/// puts in a specified amount of characters to the stream
void fillLeadingChars(char c, unsigned numChars,
                      llvm::raw_string_ostream &stream) {
  stream << std::string(numChars, c);
}

/// puts formated index (correct width) into the stream
void getIdxStr(Expr idx, unsigned width, llvm::raw_string_ostream &stream) {

  mpz_class num = 0;

  if (getNum(idx, num)) {
    unsigned desiredNumDigits = std::ceil((float)width / 4);

    unsigned numDigits = std::ceil((float)num.sizeInBase(16));

    if (numDigits < desiredNumDigits) {
      fillLeadingChars('0', desiredNumDigits - numDigits, stream);
    }

    stream << num.to_string(16);

  } else {
    stream << idx;
  }
}

/// puts formated value (correct width and spacing) into the stream
static void getValueStr(Expr value, unsigned width, bool includeAscii,
                        llvm::raw_string_ostream &stream) {

  mpz_class num = 0;
  if (getNum(value, num)) {

    unsigned numBytes =
        std::ceil((float)num.sizeInBase(16) /
                  2); // number of bytes that the value's number actually has

    unsigned desiredNumBytes = std::ceil(
        (float)width /
        8); // number of bytes that the value should have - based on its width

    if (desiredNumBytes < numBytes) {
      desiredNumBytes = numBytes;
    }

    std::vector<uint8_t> bytes(desiredNumBytes);

    // fill in the leading zeroesi
    for (int i = 0; i < (desiredNumBytes - numBytes); i++) {
      bytes[i] = 0;
    }

    // populate bytes with every byte that is in the number
    num.mpzExport(&bytes[desiredNumBytes - numBytes], nullptr, 1, 1, 1,
                  0); // 1:most sig word first, 1 byte/word, 1: each byte has
                      // most sig byte first, 0: nails bit unused

    if (includeAscii) {
      stream << format_bytes_with_ascii(bytes, None, desiredNumBytes, 1, 0,
                                        false);
    } else {
      stream << format_bytes(bytes, None, desiredNumBytes, 1, 0, false);
    }
  } else {
    stream << value;
  }
}
} // namespace kvUtils

namespace expr {
namespace hexDump {

KeyValue::KeyValue(Expr idx, Expr value, bool isRepeated)
    : m_pair(idx, value), m_isRepeated(isRepeated) {}

bool KeyValue::isSortable() const { return kvUtils::isNumeric(m_pair.first); }

template <typename T>
void KeyValue::print(T &OS, std::pair<unsigned, unsigned> widths,
                     bool includeAscii) const {

  std::string str = "";
  llvm::raw_string_ostream stream(str);

  kvUtils::getIdxStr(m_pair.first, widths.first, stream);
  stream << ": ";
  kvUtils::getValueStr(m_pair.second, widths.second, includeAscii, stream);

  OS << stream.str();
}

/// \note assumes that the index is numeric
mpz_class KeyValue::getIdxNum() const {
  assert(kvUtils::isNumeric(m_pair.first));
  mpz_class returnValue = 0;
  kvUtils::getNum(m_pair.first, returnValue);

  return returnValue;
}

/// converts indices to strings. Compares first by string size and then
/// lexicographically
bool KeyValue::operator<(KeyValue const &kv) const {
  mpz_class num1 = 0;
  mpz_class num2 = 0;

  std::string s1 = "";
  std::string s2 = "";

  if (kvUtils::getNum(m_pair.first, num1)) {
    s1 = num1.to_string(10);
  } else {
    std::stringstream ss;
    ss << m_pair.first;
    s1 = ss.str();
  }

  if (kvUtils::getNum(kv.m_pair.first, num2)) {
    s2 = num2.to_string(10);
  } else {
    std::stringstream ss;
    ss << kv.m_pair.first;
    s2 = ss.str();
  }

  if (s1.size() == s2.size()) {
    return s1 < s2;
  }

  return s1.size() < s2.size();
}

std::ostream &operator<<(std::ostream &OS, KeyValue const &kv) {
  kv.print(OS);

  return OS;
}

/**
 * stores a set of KeyValue objects
 */
class Pairs {

  std::set<KeyValue> m_set;

  Expr m_defaultValue;

  std::pair<unsigned, unsigned> m_widths;
  unsigned m_addressesPerWord = 1;

  static void store(Expr &exp, unsigned &widthDest) {
    unsigned width = 0;
    if (bv::isBvNum(exp, width)) { // note: isBvNum stores the width
      exp = exp->first();
    } else {
      mpz_class num = 0;
      if (kvUtils::getNum(exp, num)) {
        width = num.sizeInBase(2);
      }
    }

    widthDest = std::max(width, widthDest);
  }

public:
  Pairs(unsigned addressesPerWord)
      : m_addressesPerWord(addressesPerWord), m_widths(0, 0) {}

  void insert(Expr idx, Expr value) {

    if (idx)
      store(idx, m_widths.first);

    if (value)
      store(value, m_widths.second);

    m_set.emplace(idx, value);
  }

  void setDefault(Expr defaultValue) {
    store(defaultValue, m_widths.second);

    m_defaultValue = defaultValue;
  }

  template <typename T> void print(T &OS, bool includeAscii) const {
    for (auto b = m_set.begin(), e = m_set.end(); b != e; b++) {
      (*b).print(OS, m_widths, includeAscii);
      OS << "\n";

      if ((*b).isRepeated()) {
        OS << "*\n";
      }
    }
  }

  /// fills in spaces between indices with the default value
  /// \note assumes that every KeyValue's index is numeric
  void fillInGaps() {
    if (!(m_defaultValue && m_set.size() > 1 && (*m_set.begin()).isSortable()))
      return;

    for (auto b = m_set.begin(); b != (std::prev(m_set.end())); b++) {
      mpz_class idx1 = (*b).getIdxNum();
      mpz_class idx2 = (*std::next(b)).getIdxNum();

      // if there is a gap in indices then fill the gap with the default value
      if ((idx2 > (idx1 + m_addressesPerWord)) && !(*b).isRepeated()) {

        bool repeats =
            idx2 > (idx1 + (m_addressesPerWord *
                            2)); // if the gap is more than double, then
                                 // the default value is repeated

        Expr nextIdx = mkTerm<mpz_class>(idx1 + m_addressesPerWord,
                                         (*b).getIdxExpr()->efac());

        b = m_set.emplace_hint(std::next(b), nextIdx, m_defaultValue, repeats);
      }
    }
  }

  std::pair<unsigned, unsigned> getWidths() const { return m_widths; }

  void setWidths(std::pair<unsigned, unsigned> widths) { m_widths = widths; }

  const_hd_iterator cbegin() const { return m_set.cbegin(); }

  const_hd_iterator cend() const { return m_set.cend(); }
};

/// classes that derive HD_BASE are visitors that find KeyValues and store them
/// into m_pairs.
class HD_BASE {
protected:
  Pairs m_pairs;

public:
  HD_BASE(unsigned addressesPerWord) : m_pairs(addressesPerWord) {}

  virtual VisitAction operator()(Expr exp) = 0;
  virtual void doneVisiting() {}

  template <typename T> void print(T &OS, bool ascii) {
    return m_pairs.print(OS, ascii);
  }

  const_hd_iterator cbegin() const { return m_pairs.cbegin(); }

  const_hd_iterator cend() const { return m_pairs.cend(); }
};

class HD_ITE : public HD_BASE {

public:
  HD_ITE(unsigned addressesPerWord) : HD_BASE(addressesPerWord) {}

  VisitAction operator()(Expr exp) override {
    if (isOp<ITE>(exp)) {
      Expr condition = exp->arg(0);
      Expr thenBranch = exp->arg(1);
      Expr elseBranch = exp->arg(2);

      assert(isOp<EQ>(condition) || isOp<NEQ>(condition));
      assert(kvUtils::isNumeric(condition->left()) !=
             kvUtils::isNumeric(
                 condition->right())); // one side of the equals is numeric. The
                                       // numeric side will be the key

      Expr key;

      if (kvUtils::isNumeric(condition->left())) {
        key = condition->left();
      } else {
        key = condition->right();
      }

      if (isOp<EQ>(condition)) {
        assert(!isOp<ITE>(thenBranch));

        m_pairs.insert(key, thenBranch);

      } else if (isOp<NEQ>(condition)) {
        assert(!isOp<ITE>(elseBranch));

        m_pairs.insert(key, elseBranch);
      }
    }

    return VisitAction::doKids();
  }
};
class HD_ARRAY : public HD_BASE {

public:
  HD_ARRAY(unsigned addressesPerWord) : HD_BASE(addressesPerWord) {}

  VisitAction operator()(Expr exp) override {

    if (isOp<STORE>(exp) || isOp<SET>(exp)) {

      Expr idx = exp->arg(1);
      Expr value = exp->arg(2);

      m_pairs.insert(idx, value);

    } else if (isOp<CONST_ARRAY>(exp)) {
      m_pairs.setDefault(exp->right());

    } else if (isOp<CONST_FINITE_MAP>(exp)) {

      if (isOp<FINITE_MAP_VAL_DEFAULT>(exp->right())) {
        m_pairs.setDefault(exp->right()->first());
      } else {
        Expr keys = exp->left();
        Expr values = exp->right();

        // maps every key in the finite set to its corresponding value
        for (auto bKey = keys->args_begin(), bVal = values->args_begin();
             bKey != keys->args_end() && bVal != values->args_end();
             bKey++, bVal++) {
          m_pairs.insert(*bKey, *bVal);
        }
      }
    }

    return VisitAction::doKids();
  }

  void doneVisiting() override { m_pairs.fillInGaps(); }
};
} // namespace hexDump
} // namespace expr

namespace expr {
namespace hexDump {

struct FindValid {
  bool foundValid = false;
  Expr validExp = nullptr;

  bool isValidType(Expr exp) {
    return isOp<ITE>(exp) || isOp<STORE>(exp) || isOp<SET>(exp);
  }

  VisitAction operator()(Expr exp) {
    if (isValidType(exp)) {
      foundValid = true;
      validExp = exp;

      return VisitAction::skipKids();
    }

    return VisitAction::doKids();
  }
};

class HexDump::Impl {
  std::unique_ptr<HD_BASE> m_visitor;

  void findType(Expr exp, unsigned addressesPerWord) {

    if (isOp<ITE>(exp)) {
      m_visitor = std::make_unique<HD_ITE>(addressesPerWord);
      visit(*m_visitor, exp); // note: HD_ITE has its own cache

      m_visitor->doneVisiting();

    } else if (isOp<STORE>(exp) || isOp<SET>(exp)) {
      m_visitor = std::make_unique<HD_ARRAY>(addressesPerWord);

      dagVisit(*m_visitor, exp);

      m_visitor->doneVisiting();
    } else {
      // if the expression is not a supported type, then this searches its
      // children for the first supported type
      Expr validType;
      FindValid find;

      dagVisit(find, exp);

      if (find.foundValid) {
        findType(find.validExp, addressesPerWord);
      }
    }
  }

public:
  Impl(Expr exp, unsigned addressesPerWord) { findType(exp, addressesPerWord); }

  const_hd_iterator cbegin() const { return m_visitor->cbegin(); }

  const_hd_iterator cend() const { return m_visitor->cend(); }

  template <typename T> void print(T &OS, bool ascii) {
    m_visitor->print(OS, ascii);
  }
};

HexDump::HexDump(Expr exp, unsigned addressesPerWord)
    : m_impl(new HexDump::Impl(exp, addressesPerWord)) {}
HexDump::~HexDump() { delete m_impl; }

const_hd_iterator HexDump::cbegin() const { return m_impl->cbegin(); }

const_hd_iterator HexDump::cend() const { return m_impl->cend(); }

template <typename T> void HexDump::print(T &OS, bool includeAscii) const {
  m_impl->print(OS, includeAscii);
}

std::ostream &operator<<(std::ostream &OS, HexDump const &hd) {
  hd.print(OS, true);
  return OS;
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, HexDump const &hd) {
  OS << boost::lexical_cast<std::string>(hd);
  return OS;
}

class StructHexDump::StructImpl {
  std::list<std::unique_ptr<HexDump>> hexDumps;

  void init(Expr exp, unsigned addressesPerWord) {
    assert(isOp<MK_STRUCT>(exp));

    // separate every child of the struct into
    // separate hex dumps
    for (auto b = exp->args_begin(), e = exp->args_end(); b != e; b++) {
      hexDumps.push_back(std::make_unique<HexDump>((*b), addressesPerWord));
    }
  }

public:
  StructImpl(Expr exp, unsigned addressesPerWord) {
    init(exp, addressesPerWord);
  }

  std::vector<const_hd_range> getRanges() const {

    std::vector<const_hd_range> ranges;

    for (auto b = hexDumps.begin(), e = hexDumps.end(); b != e; b++) {
      const_hd_range r((*b)->cbegin(), (*b)->cend());
      ranges.push_back(r);
    }

    return ranges;
  }

  template <typename T> void print(T &OS, bool ascii) {
    for (auto b = hexDumps.begin(), e = hexDumps.end(); b != e; b++) {
      (*b)->print(OS, ascii);
      OS << "\n";
    }
  }
};

StructHexDump::StructHexDump(Expr exp, unsigned addressesPerWord)
    : m_impl(new StructHexDump::StructImpl(exp, addressesPerWord)) {}

StructHexDump::~StructHexDump() { delete m_impl; }

std::vector<const_hd_range> StructHexDump::getRanges() const {
  return m_impl->getRanges();
}

template <typename T>
void StructHexDump::print(T &OS, bool includeAscii) const {
  m_impl->print(OS, includeAscii);
}

std::ostream &operator<<(std::ostream &OS, StructHexDump const &hd) {
  hd.print(OS, true);
  return OS;
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, StructHexDump const &hd) {
  OS << boost::lexical_cast<std::string>(hd);
  return OS;
}

} // namespace hexDump
} // namespace expr
