//
// Wrapper over doctest.h to workaround macro name clash with Sealog.hh
//

#ifndef SEAHORN_SEA_DOCTEST_HH
#define SEAHORN_SEA_DOCTEST_HH

// workaround(test): to avoid name clash with doctest.h
#undef WARN
#undef INFO
#include "doctest.h"
#endif // SEAHORN_SEA_DOCTEST_HH
