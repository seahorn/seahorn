#undef SEA_ASSERT


#if defined(SEA_DISABLE_ASSERTS) || defined(NDEBUG)
#define SEA_ASSERT(a) ((void)0)
#else
#define SEA_ASSERT(a)                                                          \
  ((a) ? ((void)0) : avy::assertion_failed(#a, __FILE__, __LINE__))
#endif

#undef SEA_VERIFY

#if defined(SEA_DISABLE_ASSERTS) || defined(NDEBUG)

#define SEA_VERIFY(a) ((void)a)

#else

#define SEA_VERIFY(a) SEA_ASSERT(a)
#endif

#undef SEA_DEBUG
#if defined(SEA_NDEBUG) || defined(NDEBUG)
#define SEA_DEBUG(CODE)                                                        \
  do {                                                                         \
  } while (0)
#else
#define SEA_DEBUG(CODE)                                                        \
  do {                                                                         \
    CODE                                                                       \
  } while (0)
#endif

#ifndef SEA_ASSERT_H_
#define SEA_ASSERT_H_

#define SEA_UNREACHABLE()                                                      \
  ::avy::assertion_failed("UNREACHABLE!", __FILE__, __LINE__)
#include <cstdlib>
#include <iostream>

namespace seahorn {
inline void __attribute__((noreturn))
assertion_failed(char const *expr, char const *file, long line) {
  std::cerr << "Error:" << file << ":" << line << ":"
            << " Assertion: " << expr << "\n";
  std::cerr.flush();
  std::abort();
}

} // namespace seahorn

#endif
