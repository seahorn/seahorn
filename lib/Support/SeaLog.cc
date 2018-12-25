#include "seahorn/Support/SeaLog.hh"

using namespace llvm;
bool seahorn::SeaWarnEnable = true;

namespace seahorn {

void SetSeaWarn(bool v) { SeaWarnEnable = v; }

warn_ostream::warn_ostream(raw_ostream &OS, const std::string &prefix,
                           const std::string &suffix)
    : raw_svector_ostream(m_buffer), m_os(OS), m_prefix(prefix),
      m_suffix(suffix) {}

warn_ostream::~warn_ostream() {
  if (!SeaWarnEnable)
    return;
  m_os << m_prefix;
  m_os << str();
#if !defined(NDEBUG)
  if (!m_suffix.empty())
    m_os << " (" << m_suffix << ")";
#endif
  m_os << "\n";
  resetColor();
}
}
