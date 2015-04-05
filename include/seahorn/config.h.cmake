#ifndef _SEAHORN_CONFIG_H
#define _SEAHORN_CONFIG_H

#define SEAHORN_VERSION_INFO "${SeaHorn_VERSION_INFO}"

/* Define whether ikos-core is available */
#cmakedefine HAVE_IKOS ${HAVE_IKOS}

/** Define whether ikos-llvm is available */
#cmakedefine HAVE_IKOS_LLVM ${HAVE_IKOS_LLVM}

/** Define whether DSA library is available */
#cmakedefine HAVE_DSA ${HAVE_DSA}

/** Define whether llvm-seahorn is available */
#cmakedefine HAVE_LLVM_SEAHORN ${HAVE_LLVM_SEAHORN}

#endif
