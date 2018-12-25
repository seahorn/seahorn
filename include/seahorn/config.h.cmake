#ifndef _SEAHORN_CONFIG_H
#define _SEAHORN_CONFIG_H

#define SEAHORN_VERSION_INFO "${SeaHorn_VERSION_INFO}"

/** Define whether crab is available */
#cmakedefine HAVE_CRAB ${HAVE_CRAB}

/** Define whether crab-llvm is available */
#cmakedefine HAVE_CRAB_LLVM ${HAVE_CRAB_LLVM}

/** Define whether DSA library is available */
#cmakedefine HAVE_DSA ${HAVE_DSA}

/** Define whether llvm-seahorn is available */
#cmakedefine HAVE_LLVM_SEAHORN ${HAVE_LLVM_SEAHORN}

/** Define whether ldd is available */
#cmakedefine HAVE_LDD ${HAVE_LDD}

#endif
