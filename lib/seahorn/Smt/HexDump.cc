#include "seahorn/Expr/HexDump.hh"

namespace expr {
namespace hexDump {

/// puts in a specified amount of characters to the stream
static void fillLeadingChars(char c, unsigned numChars,
                             llvm::raw_string_ostream &stream) {
  stream << std::string(numChars, c);
}

void getContentStr(Expr value, unsigned desiredNumBytes, bool includeAscii,
                   llvm::raw_string_ostream &stream) {
  mpz_class num = 0;
  if (expr::numeric::getNum(value, num)) {

    unsigned numBytes =
        std::ceil((float)num.sizeInBase(16) /
                  2); // number of bytes that the value's number actually has

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
    stream << *value;
  }
}

void getIdxStr(Expr idx, unsigned desiredNumBytes,
               llvm::raw_string_ostream &stream) {
  mpz_class num = 0;

  if (expr::numeric::getNum(idx, num)) {
    unsigned desiredNumDigits = desiredNumBytes * 2;

    unsigned numDigits = std::ceil((float)num.sizeInBase(16));

    if (numDigits < desiredNumDigits) {
      fillLeadingChars('0', desiredNumDigits - numDigits, stream);
    }

    stream << num.to_string(16);

  } else {
    stream << *idx;
  }
}

void getCellStr(const MemCell &cell, llvm::raw_string_ostream &stream,
                size_t idWidth, size_t contentWidth, bool includeAscii,
                bool isDefault) {
  if (isDefault) {
    stream << "*";
  } else {
    getIdxStr(cell.getIdxExpr(), idWidth, stream);
  }
  stream << ": ";
  getContentStr(cell.getValueExpr(), contentWidth, includeAscii, stream);
  stream << "\n";
}

void HexDump::fillInGaps() {
  // fill gaps if default value is available
  if (!m_cells.getDefault())
    return;
  if (m_cells.size() == 0) {
    m_cells.insert(mkTerm<std::string>("*", m_cells.getDefault()->efac()),
                   m_cells.getDefault());
    return;
  }

  // gap only possible if more than 1 items
  if (m_cells.size() <= 1 || !(*m_cells.cbegin()).isSortable())
    return;

  size_t gapSize = m_cells.isAligned() ? m_cells.getContentWidth() : 1;
  // go through IDed values
  for (auto b = m_cells.cbegin(); b != std::prev(m_cells.cend()); b++) {
    mpz_class idx1 = (*b).getIdxNum();
    mpz_class idx2 = (*std::next(b)).getIdxNum();

    // if there is a gap in indices then fill the gap with the default value
    if ((idx2 > (idx1 + gapSize)) && !(*b).isRepeated()) {

      bool repeats =
          idx2 > (idx1 + (gapSize * 2)); // if the gap is more than double,
                                         // then the default value is repeated

      Expr defaultID =
          mkTerm<mpz_class>(idx1 + gapSize, (*b).getIdxExpr()->efac());
      Expr defaultVal = m_cells.getDefault();
      m_cells.insert(defaultID, defaultVal, repeats);
      b = std::next(b);
    }
  }
}

template <typename T> void HexDump::print(T &OS, bool includeAscii) const {
  if (!isValid()) {
    // expr is not readable by visitor
    OS << *m_expr;
    return;
  }

  std::string s("");
  llvm::raw_string_ostream stream(s);

  for (auto b = m_cells.cbegin(); b != m_cells.cend(); b++) {
    getCellStr(*b, stream, m_cells.getIdWidth(), m_cells.getContentWidth(),
               includeAscii);
    if (b->isRepeated())
      stream << "*\n";
  }
  OS << stream.str();
}

std::ostream &operator<<(std::ostream &OS, HexDump const &hd) {
  hd.print(OS, true);
  return OS;
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, HexDump const &hd) {
  hd.print(OS, true);
  return OS;
}

StructHexDump::StructHexDump(Expr exp) {
  m_exp = exp;
  assert(isOp<MK_STRUCT>(exp));

  // separate every child of the struct into
  // separate hex dumps
  for (auto *b : *exp)
    hexDumps.push_back(std::make_unique<HexDump>(b));
}

std::vector<const_mc_range> StructHexDump::getRanges() const {
  std::vector<const_mc_range> ranges;
  for (auto b = hexDumps.begin(), e = hexDumps.end(); b != e; b++) {
    const_mc_range r((*b)->cbegin(), (*b)->cend());
    ranges.push_back(r);
  }
  return ranges;
}

template <typename T>
void StructHexDump::print(T &OS, bool includeAscii) const {
  if (!hexDumps.front()->isValid()) {
    OS << *m_exp;
    return;
  }

  for (auto &b : hexDumps) {
    b->print(OS, includeAscii);
    OS << "\n";
  }
}

llvm::raw_ostream &operator<<(llvm::raw_ostream &OS, StructHexDump const &shd) {
  shd.print(OS, true);
  return OS;
}

std::ostream &operator<<(std::ostream &OS, StructHexDump const &shd) {
  shd.print(OS, true);
  return OS;
}

} // namespace hexDump
} // namespace expr
