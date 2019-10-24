# - Try to find yices2
# Once done this will define
#  YICES2_FOUND - System has yices2
#  YICES2_INCLUDE_DIRS - The yices2 include directories
#  YICES2_LIBRARIES - The libraries needed to use yices2
#  YICES2_EXECUTABLE - The yices2 executable

if (YICES2_HOME)
  find_path(YICES2_INCLUDE_DIR yices.h PATHS "${YICES2_HOME}/include")
else() 
  find_path(YICES2_INCLUDE_DIR yices.h)
endif()

if (YICES2_HOME)
  find_library(YICES2_LIBRARY yices PATHS "${YICES2_HOME}/lib")
else() 
  find_library(YICES2_LIBRARY yices)
endif()

if (YICES2_HOME)
  find_program(YICES2_EXECUTABLE yices-smt2 PATHS "${YICES2_HOME}/bin")
else() 
  find_program(YICES2_EXECUTABLE yices-smt2)
endif()

# If library found, check the version
if (YICES2_INCLUDE_DIR AND Yices2_FIND_VERSION)

  # Check version. It is in yices.h of the form 
  # 
  # #define __YICES_VERSION            2
  # #define __YICES_VERSION_MAJOR      3
  # #define __YICES_VERSION_PATCHLEVEL 0

  # Extract version lines from yices.h
  file(STRINGS "${YICES2_INCLUDE_DIR}/yices.h" __YICES_H_VERSIONS REGEX "#define __YICES_VERSION")
  foreach(v __YICES_VERSION __YICES_VERSION_MAJOR __YICES_VERSION_PATCHLEVEL)
    if("${__YICES_H_VERSIONS}" MATCHES ".*#define ${v}[ ]+([0-9]+).*")
      set(${v} "${CMAKE_MATCH_1}")
    endif()
  endforeach()

  set(__YICES_H_VERSION "${__YICES_VERSION}.${__YICES_VERSION_MAJOR}.${__YICES_VERSION_PATCHLEVEL}")

  # Compare the found version to asked for version
  if ("${__YICES_H_VERSION}" VERSION_LESS "${Yices2_FIND_VERSION}")
     unset(YICES2_INCLUDE_DIR CACHE)
     unset(YICES2_LIBRARY CACHE)
     unset(YICES2_EXECUTABLE CACHE)
  elseif (Yices2_FIND_VERSION_EXACT AND NOT "${__YICES_H_VERSION}" VERSION_EQUAL "${Yices2_FIND_VERSION}")
     unset(YICES2_INCLUDE_DIR CACHE)
     unset(YICES2_LIBRARY CACHE)
     unset(YICES2_EXECUTABLE CACHE)
  endif()
endif()

set(YICES2_LIBRARIES ${YICES2_LIBRARY})
set(YICES2_INCLUDE_DIRS ${YICES2_INCLUDE_DIR})

include(FindPackageHandleStandardArgs)
find_package_handle_standard_args(Yices2 DEFAULT_MSG YICES2_LIBRARY YICES2_INCLUDE_DIR YICES2_EXECUTABLE)

mark_as_advanced(YICES2_INCLUDE_DIR YICES2_LIBRARY YICES2_EXECUTABLE) 
