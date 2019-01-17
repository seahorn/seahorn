/** \brief Rudimentary logging facility for warnings and errors

 Prints in color with Warning/Error prefix and file location suffix.
 Usage:

    WARN << message;

  Note that message should not be terminated by newline
*/
#pragma once
#include "llvm/Support/Path.h"
#include "llvm/Support/raw_ostream.h"

#define FLOC(X, Y) llvm::sys::path::filename(X) + ":" + llvm::Twine(Y)
#define WARN                                                                   \
  seahorn::warn_ostream(llvm::errs())                                          \
      .color(llvm::raw_ostream::YELLOW)                                        \
      .suffix(FLOC(__FILE__, __LINE__))
#define ERR                                                                    \
  seahorn::warn_ostream(llvm::errs())                                          \
      .color(llvm::raw_ostream::RED)                                           \
      .prefix("Error: ")                                                       \
      .suffix(FLOC(__FILE__, __LINE__))

namespace seahorn {
/// \brief Enables warning log stream
extern bool SeaWarnEnable;

void SetSeaWarn(bool v);

class warn_ostream : public llvm::raw_svector_ostream {
  llvm::raw_ostream &m_os;
  llvm::SmallVector<char, 0> m_buffer;
  std::string m_prefix;
  std::string m_suffix;

public:
  warn_ostream(llvm::raw_ostream &OS, const std::string &prefix = "Warning: ",
               const std::string &suffix = "");
  ~warn_ostream() override;

  warn_ostream &prefix(const std::string &v) {
    m_prefix = v;
    return *this;
  }
  warn_ostream &prefix(const std::string &&v) {
    m_prefix = v;
    return *this;
  }

  warn_ostream &suffix(const std::string &v) {
    m_suffix = v;
    return *this;
  }
  warn_ostream &suffix(const std::string &&v) {
    m_suffix = v;
    return *this;
  }
  warn_ostream &suffix(const llvm::Twine &v) {
    m_suffix = v.str();
    return *this;
  }

  warn_ostream &color(enum Colors color) {
    changeColor(color);
    return *this;
  }

  llvm::raw_ostream &changeColor(enum Colors color, bool bold = false,
                                 bool bg = false) override {
    if (SeaWarnEnable && m_os.has_colors())
      m_os.changeColor(color, bold, bg);
    return *this;
  }

  llvm::raw_ostream &resetColor() override {
    if (SeaWarnEnable && m_os.has_colors())
      m_os.resetColor();
    return *this;
  }

  llvm::raw_ostream &reverseColor() override {
    if (SeaWarnEnable && m_os.has_colors())
      m_os.reverseColor();
    return *this;
  }
};
} // namespace seahorn
