if (NOT GMP_FOUND)
  set(GMP_SEARCH_PATH "" CACHE PATH "Search path for gmp.")
  find_path(GMP_INCLUDE_DIR NAMES gmp.h PATHS ${GMP_SEARCH_PATH}/include)
  find_library(GMP_LIB NAMES gmp PATHS ${GMP_SEARCH_PATH}/lib)

  mark_as_advanced(GMP_SEARCH_PATH
    GMP_INCLUDE_DIR GMP_LIB)

  include (FindPackageHandleStandardArgs)
  find_package_handle_standard_args(Gmp
    REQUIRED_VARS GMP_INCLUDE_DIR GMP_LIB )
endif()
