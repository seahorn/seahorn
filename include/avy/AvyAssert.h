#undef AVY_ASSERT

#if defined(AVY_DISABLE_ASSERTS) || defined(NDEBUG)
# define AVY_ASSERT(a) ((void)0)
#else
# define AVY_ASSERT(a) ((a)                                            \
                         ? ((void)0)                                    \
                         : avy::assertion_failed(#a, __FILE__, __LINE__))
#endif

#undef AVY_VERIFY

#if defined(AVY_DISABLE_ASSERTS) || defined(NDEBUG)

#define AVY_VERIFY(a) ((void)a)

#else

#define AVY_VERIFY(a) AVY_ASSERT(a)
#endif 

#undef AVY_DEBUG
#if defined(AVY_NDEBUG) || defined(NDEBUG)
#define AVY_DEBUG(CODE) do { } while (0)
#else
#define AVY_DEBUG(CODE) do { CODE } while (0)
#endif


#ifndef AVY_ASSERT_H_
#define AVY_ASSERT_H_

#define AVY_UNREACHABLE() ::avy::assertion_failed("UNREACHABLE!", __FILE__, __LINE__)
#include <cstdlib>
#include <iostream>

namespace avy
{
  inline void __attribute__ ((noreturn))  assertion_failed (char const *expr, char const * file, long line) 
  {
    std::cerr << "Error:" << file << ":" << line << ":" 
              << " Assertion: " << expr << "\n";
    std::cerr.flush ();
    std::abort ();
  }
  
}

#endif

