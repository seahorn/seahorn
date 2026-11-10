# - Try to find Bitwuzla (https://bitwuzla.github.io)
# Once done this will define
#  BITWUZLA_FOUND - System has a usable Bitwuzla
#  BITWUZLA_INCLUDE_DIR - The directory containing bitwuzla/cpp/bitwuzla.h
#  BITWUZLA_LIBRARY - The Bitwuzla shared library
#  BITWUZLA_VERSION - The version, read from the bitwuzla.pc installed next
#                     to the library, or else from bitwuzla::version()
#
# If BITWUZLA_HOME is set, only that installation is searched. Otherwise the
# search order is Bitwuzla_ROOT, CMAKE_PREFIX_PATH, the libdir that
# pkg-config reports for bitwuzla, and the system prefixes (e.g.
# /opt/homebrew, /usr/local, /usr). The first library found is the one
# checked: if it is unusable, no other installation is tried.

# Search again on every configure. The result depends on several settings
# and environment variables, and a cached path would hide a change to any
# of them.
unset(BITWUZLA_INCLUDE_DIR CACHE)
unset(BITWUZLA_LIBRARY CACHE)

# SeaHorn puts .a first in CMAKE_FIND_LIBRARY_SUFFIXES. Ask for the shared
# library by its full name first.
set(_BITWUZLA_NAMES
  ${CMAKE_SHARED_LIBRARY_PREFIX}bitwuzla${CMAKE_SHARED_LIBRARY_SUFFIX} bitwuzla)

if (BITWUZLA_HOME)
  # Meson may install into lib/<multiarch> on Debian and Ubuntu.
  find_library(BITWUZLA_LIBRARY NAMES ${_BITWUZLA_NAMES}
    PATHS "${BITWUZLA_HOME}/lib" "${BITWUZLA_HOME}/lib64"
          "${BITWUZLA_HOME}/lib/${CMAKE_LIBRARY_ARCHITECTURE}"
    NO_DEFAULT_PATH)
else()
  # Only the libdir is asked for: pkg-config answers it even when the .pc
  # files of gmp and mpfr, which bitwuzla.pc requires, are missing.
  unset(_BITWUZLA_PC_LIBDIR)
  find_package(PkgConfig QUIET)
  if (PKG_CONFIG_FOUND)
    execute_process(COMMAND ${PKG_CONFIG_EXECUTABLE} --variable=libdir bitwuzla
      OUTPUT_VARIABLE _BITWUZLA_PC_LIBDIR OUTPUT_STRIP_TRAILING_WHITESPACE
      ERROR_QUIET)
  endif()
  find_library(BITWUZLA_LIBRARY NAMES ${_BITWUZLA_NAMES}
    HINTS ${_BITWUZLA_PC_LIBDIR})
endif()

# A static libbitwuzla.a (the default of Bitwuzla's configure.py) also needs
# libbitwuzla{ls,bv,bb}, the SAT solvers, GMP and MPFR. Only the shared
# library is supported.
if (BITWUZLA_LIBRARY MATCHES "\\${CMAKE_STATIC_LIBRARY_SUFFIX}$")
  message(WARNING "Ignoring static ${BITWUZLA_LIBRARY}: "
    "build Bitwuzla with ./configure.py --shared")
  unset(BITWUZLA_LIBRARY CACHE)
  set(BITWUZLA_LIBRARY BITWUZLA_LIBRARY-NOTFOUND)
endif()

# Take the header and the version from the library's own installation, so
# that one installation's header is never paired with another's library. The
# library is in <prefix>/lib, <prefix>/lib64 or <prefix>/lib/<multiarch>.
unset(BITWUZLA_VERSION)
if (BITWUZLA_LIBRARY)
  get_filename_component(_BITWUZLA_LIBDIR "${BITWUZLA_LIBRARY}" DIRECTORY)
  if (CMAKE_LIBRARY_ARCHITECTURE AND
      _BITWUZLA_LIBDIR MATCHES "/lib/${CMAKE_LIBRARY_ARCHITECTURE}$")
    get_filename_component(_BITWUZLA_PREFIX "${_BITWUZLA_LIBDIR}/../.." ABSOLUTE)
  else()
    get_filename_component(_BITWUZLA_PREFIX "${_BITWUZLA_LIBDIR}/.." ABSOLUTE)
  endif()
  find_path(BITWUZLA_INCLUDE_DIR bitwuzla/cpp/bitwuzla.h
    PATHS "${_BITWUZLA_PREFIX}/include" NO_DEFAULT_PATH)
  if (EXISTS "${_BITWUZLA_LIBDIR}/pkgconfig/bitwuzla.pc")
    file(STRINGS "${_BITWUZLA_LIBDIR}/pkgconfig/bitwuzla.pc" _BITWUZLA_PC_VERSION
      REGEX "^Version:")
    string(REGEX REPLACE "^Version:[ \t]*" "" BITWUZLA_VERSION
      "${_BITWUZLA_PC_VERSION}")
  endif()
endif()

# Without bitwuzla.pc, ask the library itself. A version that cannot be
# determined is not accepted when a minimum version is required: the test
# program below would also accept an older release with the same C++ API.
if (BITWUZLA_LIBRARY AND BITWUZLA_INCLUDE_DIR AND NOT BITWUZLA_VERSION)
  set(_BITWUZLA_VERSION_SRC
    "${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/BitwuzlaVersion.cpp")
  file(WRITE "${_BITWUZLA_VERSION_SRC}" "
#include \"bitwuzla/cpp/bitwuzla.h\"
#include <cstdio>
int main() { std::printf(\"%s\", bitwuzla::version()); return 0; }
")
  try_run(_BITWUZLA_VERSION_RUNS _BITWUZLA_VERSION_COMPILES
    "${CMAKE_BINARY_DIR}${CMAKE_FILES_DIRECTORY}/BitwuzlaVersion"
    "${_BITWUZLA_VERSION_SRC}"
    CMAKE_FLAGS "-DINCLUDE_DIRECTORIES=${BITWUZLA_INCLUDE_DIR}"
    LINK_LIBRARIES "${BITWUZLA_LIBRARY}"
    CXX_STANDARD 17
    RUN_OUTPUT_VARIABLE _BITWUZLA_VERSION_OUT)
  if (_BITWUZLA_VERSION_COMPILES AND "${_BITWUZLA_VERSION_RUNS}" STREQUAL "0" AND
      _BITWUZLA_VERSION_OUT MATCHES "^([0-9]+(\\.[0-9]+)*)")
    set(BITWUZLA_VERSION "${CMAKE_MATCH_1}")
  elseif (Bitwuzla_FIND_VERSION)
    message(WARNING "Ignoring ${BITWUZLA_LIBRARY}: its version is unknown "
      "(there is no bitwuzla.pc, and a program printing "
      "bitwuzla::version() does not run)")
    unset(BITWUZLA_LIBRARY CACHE)
    set(BITWUZLA_LIBRARY BITWUZLA_LIBRARY-NOTFOUND)
  endif()
endif()

# Check that a program using the C++ API compiles and links with SeaHorn's
# compiler and flags. This rejects, e.g., a library built for another
# architecture or against another C++ standard library. The result is cached
# until the library, the header directory, the compiler or the flags change.
# A version that is known to be too old is left to the version check below,
# which reports it more clearly.
if (BITWUZLA_VERSION AND Bitwuzla_FIND_VERSION AND
    BITWUZLA_VERSION VERSION_LESS Bitwuzla_FIND_VERSION)
  set(_BITWUZLA_TOO_OLD TRUE)
else()
  set(_BITWUZLA_TOO_OLD FALSE)
endif()
if (BITWUZLA_LIBRARY AND BITWUZLA_INCLUDE_DIR AND NOT _BITWUZLA_TOO_OLD)
  set(_BITWUZLA_LINK_KEY "${BITWUZLA_LIBRARY};${BITWUZLA_INCLUDE_DIR};${CMAKE_CXX_COMPILER};${CMAKE_CXX_FLAGS};${CMAKE_CXX_STANDARD};${CMAKE_EXE_LINKER_FLAGS}")
  if (NOT "${_BITWUZLA_LINK_KEY}" STREQUAL "${_BITWUZLA_LINK_CHECKED}")
    unset(BITWUZLA_LINKS CACHE)
  endif()
  include(CMakePushCheckState)
  include(CheckCXXSourceCompiles)
  cmake_push_check_state(RESET)
  set(CMAKE_REQUIRED_INCLUDES "${BITWUZLA_INCLUDE_DIR}")
  set(CMAKE_REQUIRED_LIBRARIES "${BITWUZLA_LIBRARY}")
  check_cxx_source_compiles("
#include \"bitwuzla/cpp/bitwuzla.h\"
int main() {
  bitwuzla::TermManager tm;
  bitwuzla::Term x = tm.mk_const(tm.mk_bv_sort(8), std::string(\"x\"));
  bitwuzla::Bitwuzla solver(tm);
  solver.assert_formula(tm.mk_term(bitwuzla::Kind::EQUAL, {x, x}));
  return solver.check_sat() == bitwuzla::Result::SAT ? 0 : 1;
}" BITWUZLA_LINKS)
  cmake_pop_check_state()
  set(_BITWUZLA_LINK_CHECKED "${_BITWUZLA_LINK_KEY}" CACHE INTERNAL "")
  if (NOT BITWUZLA_LINKS)
    message(WARNING "Ignoring ${BITWUZLA_LIBRARY}: a test program does not "
      "compile and link against it with ${CMAKE_CXX_COMPILER} and "
      "CMAKE_CXX_FLAGS. The compiler output is in CMakeFiles/ of the build "
      "directory (CMakeConfigureLog.yaml or CMakeError.log).")
    unset(BITWUZLA_LIBRARY CACHE)
    set(BITWUZLA_LIBRARY BITWUZLA_LIBRARY-NOTFOUND)
  endif()
endif()

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Bitwuzla
  REQUIRED_VARS BITWUZLA_LIBRARY BITWUZLA_INCLUDE_DIR
  VERSION_VAR BITWUZLA_VERSION)

mark_as_advanced(BITWUZLA_INCLUDE_DIR BITWUZLA_LIBRARY)
