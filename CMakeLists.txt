cmake_minimum_required(VERSION 2.8.11)

project (SeaHorn)
set (SeaHorn_VERSION_MAJOR 0)
set (SeaHorn_VERSION_MINOR 1)
set (SeaHorn_VERSION_PATCH 0)
set (SeaHorn_VERSION_TWEAK "rc3")

if (NOT PACKAGE_VERSION)
  set(PACKAGE_VERSION
    "${SeaHorn_VERSION_MAJOR}.${SeaHorn_VERSION_MINOR}.${SeaHorn_VERSION_PATCH}")
  if (DEFINED SeaHorn_VERSION_TWEAK)
    set (PACKAGE_VERSION "${PACKAGE_VERSION}-${SeaHorn_VERSION_TWEAK}")
  endif()
  set (SeaHorn_VERSION_INFO ${PACKAGE_VERSION})
endif()


if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR )
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")
endif()

enable_testing()
include (CTest)

# Default is release with debug info
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
    "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
endif()

# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

find_package (Git)
if (GIT_FOUND)
  set (SEAHORN_LLVM_REPO "https://github.com/seahorn/llvm-seahorn"
    CACHE STRING "seahorn-llvm repo")
  set (LLVM_DSA_REPO "https://github.com/seahorn/llvm-dsa"
    CACHE STRING "llvm-dsa repo")
  set (SEA_DSA_REPO "https://github.com/seahorn/sea-dsa"
    CACHE STRING "sea-dsa repo")
  set (CRAB_LLVM_REPO "https://github.com/seahorn/crab-llvm"
    CACHE STRING "crab-llvm repo")
  
  add_custom_target (seahorn-llvm-git
    ${GIT_EXECUTABLE} clone ${SEAHORN_LLVM_REPO} ${CMAKE_SOURCE_DIR}/llvm-seahorn)
  add_custom_target (llvm-dsa-git
    ${GIT_EXECUTABLE} clone ${LLVM_DSA_REPO} ${CMAKE_SOURCE_DIR}/llvm-dsa)
  add_custom_target (sea-dsa-git
    ${GIT_EXECUTABLE} clone ${SEA_DSA_REPO} ${CMAKE_SOURCE_DIR}/sea-dsa)
  add_custom_target (crab-llvm-git
    ${GIT_EXECUTABLE} clone ${CRAB_LLVM_REPO} ${CMAKE_SOURCE_DIR}/crab-llvm)
  add_custom_target (extra
    ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
    DEPENDS seahorn-llvm-git llvm-dsa-git sea-dsa-git crab-llvm-git)

else()
  message (STATUS "Could not find git. Not adding 'extra' target.")
endif()


option (SEAHORN_STATIC_EXE "Static executable." OFF)

set (CUSTOM_BOOST_ROOT "" CACHE PATH "Path to custom boost installation.")
if (CUSTOM_BOOST_ROOT)
  set (BOOST_ROOT ${CUSTOM_BOOST_ROOT})
  set (Boost_NO_SYSTEM_PATHS "ON")
endif()

# put static libraries first
set(CMAKE_FIND_LIBRARY_SUFFIXES ".a" ${CMAKE_FIND_LIBRARY_SUFFIXES})

option (UNIT_TESTS "Compile unit tests" OFF)
set (Boost_USE_STATIC_LIBS ON)
set (BOOST_COMPONENTS system)
if (UNIT_TESTS)
  set (BOOST_COMPONENTS ${BOOST_COMPONENTS} unit_test_framework)
endif()
  find_package (Boost 1.55 REQUIRED COMPONENTS ${BOOST_COMPONENTS})
if (Boost_FOUND)
  include_directories (${Boost_INCLUDE_DIRS})
endif ()

include(ExternalProject)
set_property(DIRECTORY PROPERTY EP_STEP_TARGETS configure build test)

set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  set(CMAKE_MACOSX_RPATH TRUE)  
endif ()  
if (NOT CMAKE_INSTALL_RPATH)
  set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
endif ()


set (Z3_TAG "origin/spacer" CACHE STRING "Z3 git tag to use")
set (Z3_REPO "https://bitbucket.org/spacer/code.git" CACHE STRING "Z3 repo")
if (CMAKE_BUILD_TYPE STREQUAL "Debug")
  set (Z3_DEBUG "-d")
else()
  set (Z3_DEBUG "")
endif()

ExternalProject_Add(z3
  GIT_REPOSITORY  ${Z3_REPO}
  GIT_TAG ${Z3_TAG}
  BUILD_IN_SOURCE 1
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CONFIGURE_COMMAND env CC=${CMAKE_C_COMPILER} CXX=${CMAKE_CXX_COMPILER}
  ./configure -p <INSTALL_DIR> -b build --staticlib ${Z3_DEBUG}
  BUILD_COMMAND make -j3 -C build
  INSTALL_COMMAND make -C build install
  COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_INSTALL 1
  LOG_BUILD 1)

find_package(Z3 4.3.2)
if (NOT Z3_FOUND)
  ExternalProject_Get_Property (z3 INSTALL_DIR)
  set(Z3_ROOT ${INSTALL_DIR} CACHE PATH "Forced location of Z3" FORCE)
  message(WARNING "No Z3 found. Run \n\tcmake --build . && cmake ${CMAKE_SOURCE_DIR}")
else()
  set_target_properties(z3 PROPERTIES EXCLUDE_FROM_ALL ON)
  include_directories(${Z3_INCLUDE_DIR})
  message ("Found Z3 at ${Z3_EXECUTABLE}")
  # indicate that we want z3 binary to be included in the binary distribution
  install (PROGRAMS ${Z3_EXECUTABLE} DESTINATION bin)
endif()

ExternalProject_Add (llvm
  SVN_REPOSITORY http://llvm.org/svn/llvm-project/llvm/tags/RELEASE_360/final/
  SOURCE_DIR ${CMAKE_SOURCE_DIR}/ext/llvm
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CMAKE_ARGS
  -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER} -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
  -DCMAKE_BUILD_TYPE:STRING=${CMAKE_BUILD_TYPE}
  -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>
  -DLLVM_TARGETS_TO_BUILD:STRING=X86 -DWITH_POLY:BOOL=OFF
  -DLLVM_ENABLE_PEDANTIC=OFF
  -DLLVM_ENABLE_PIC=ON -DLLVM_REQUIRES_RTTI:BOOL=TRUE
  TEST_AFTER_INSTALL 1
  TEST_COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_BUILD 1
  LOG_INSTALL 1)

find_package (LLVM 3.6.0 CONFIG NO_DEFAULT_PATH)
if (NOT LLVM_FOUND)
  ExternalProject_Get_Property (llvm INSTALL_DIR)
  set (LLVM_ROOT ${INSTALL_DIR})
  set (LLVM_DIR ${LLVM_ROOT}/share/llvm/cmake CACHE PATH
    "Forced location of LLVM cmake config" FORCE)
  message (WARNING "No llvm found. Run \n\tcmake --build . && cmake ${CMAKE_SOURCE_DIR}")
  return()
else()
  set_target_properties(llvm PROPERTIES EXCLUDE_FROM_ALL ON)

  message(STATUS "Found LLVM ${LLVM_PACKAGE_VERSION}")
  message(STATUS "Using LLVMConfig.cmake in: ${LLVM_DIR}")

  # We incorporate the CMake features provided by LLVM:
  list(APPEND CMAKE_MODULE_PATH "${LLVM_CMAKE_DIR}")
  include(AddLLVM)
  include(HandleLLVMOptions)
  set(LLVM_RUNTIME_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/${CMAKE_CFG_INTDIR}/bin)
  set(LLVM_LIBRARY_OUTPUT_INTDIR ${CMAKE_BINARY_DIR}/${CMAKE_CFG_INTDIR}/lib)

  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${LLVM_CXXFLAGS}")
  set(CMAKE_EXE_LINKER_FLAGS "${CMAKE_EXE_LINKER_FLAGS} ${LLVM_LDFLAGS}")

  set(LLVM_REQUIRES_RTTI TRUE)
  set(LLVM_REQUIRES_EH TRUE)

  include_directories(${LLVM_INCLUDE_DIRS})
  link_directories(${LLVM_LIBRARY_DIRS})
  add_definitions(${LLVM_DEFINITIONS})

endif()

set (PACKAGE_NAME SeaHorn)
set(PACKAGE_STRING "${PACKAGE_NAME} ${PACKAGE_VERSION}")

# Configure CPack.
include(TargetArch)
target_architecture(CMAKE_TARGET_ARCH)
message ("arch: ${CMAKE_TARGET_ARCH}")
set(CPACK_PACKAGE_INSTALL_DIRECTORY "SeaHorn")
set(CPACK_PACKAGE_VENDOR "SeaHorn")
set(CPACK_PACKAGE_VERSION_MAJOR ${SeaHorn_VERSION_MAJOR})
set(CPACK_PACKAGE_VERSION_MINOR ${SeaHorn_VERSION_MINOR})
set(CPACK_PACKAGE_VERSION_PATCH ${SeaHorn_VERSION_PATCH})
set(CPACK_PACKAGE_VERSION ${PACKAGE_VERSION})
set(CPACK_RESOURCE_FILE_LICENSE "${CMAKE_CURRENT_SOURCE_DIR}/license.txt")
set(CPACK_RESOURCE_FILE_README "${CMAKE_CURRENT_SOURCE_DIR}/README.md")
set(CPACK_PACKAGE_DESCRIPTION_FILE "${CMAKE_CURRENT_SOURCE_DIR}/README.md")
if(CMAKE_BUILD_TYPE STREQUAL Release)
  set(CPACK_PACKAGE_FILE_NAME
    "${CMAKE_PROJECT_NAME}-${CPACK_PACKAGE_VERSION}-${CMAKE_SYSTEM_NAME}-${CMAKE_TARGET_ARCH}")
else()
  set(CPACK_PACKAGE_FILE_NAME
    "${CMAKE_PROJECT_NAME}-${CPACK_PACKAGE_VERSION}-${CMAKE_SYSTEM_NAME}-${CMAKE_TARGET_ARCH}-${CMAKE_BUILD_TYPE}")
endif()
if(WIN32 AND NOT UNIX)
  set(CPACK_NSIS_MODIFY_PATH "ON")
  set(CPACK_NSIS_ENABLE_UNINSTALL_BEFORE_INSTALL "ON")
  set(CPACK_NSIS_EXTRA_INSTALL_COMMANDS
    "ExecWait '$INSTDIR/tools/msbuild/install.bat'")
  set(CPACK_NSIS_EXTRA_UNINSTALL_COMMANDS
    "ExecWait '$INSTDIR/tools/msbuild/uninstall.bat'")
endif()
include(CPack)

install (FILES ${CMAKE_CURRENT_SOURCE_DIR}/README.md DESTINATION .)
# install all the licenses
install (FILES  ${CMAKE_CURRENT_SOURCE_DIR}/license.txt
  DESTINATION share/doc/seahorn
  RENAME seahorn_license.txt)

if (EXISTS z3-prefix/src/z3/LICENSE.txt)
  install (
    FILES
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/LICENSE.txt
    DESTINATION share/doc/seahorn
    RENAME z3_license.txt)
endif()

if (EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/ext/llvm/LICENSE.TXT)
  install (FILES ext/llvm/LICENSE.TXT
    DESTINATION share/doc/seahorn
    RENAME llvm_license.txt)
endif()

if (EXISTS ${CMAKE_CURRENT_BINARY_DIR}/llvm-prefix/src/llvm-build/bin/clang-3.6)
  install (
    PROGRAMS
    ${CMAKE_CURRENT_BINARY_DIR}/llvm-prefix/src/llvm-build/bin/clang-3.6
    DESTINATION bin)
endif()

if (EXISTS ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build)
  file(GLOB z3py
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.py?
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.py?
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.so
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.dylib
    ${CMAKE_CURRENT_BINARY_DIR}/z3-prefix/src/z3/build/*.dll
    )
  install(FILES ${z3py} DESTINATION lib/z3py)
endif()

if (EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/crab-llvm/LICENSE)
  install (FILES crab-llvm/LICENSE
    DESTINATION share/doc/seahorn
    RENAME crab_llvm_license.txt)
endif()

if (EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/share/seahorn.h)
  install (FILES share/seahorn.h
    DESTINATION share/)
  install (FILES share/seahorn.c
    DESTINATION share/)
endif()

# check for rt lib. Not needed on OSX.
find_library(RT_LIB NAMES rt)
if (NOT RT_LIB)
  set(RT_LIB "")
endif()
mark_as_advanced(RT_LIB)

find_package(Curses)

find_package(Gmp REQUIRED)
if (GMP_FOUND)
  include_directories (${GMP_INCLUDE_DIR})
  include_directories (${GMPXX_INCLUDE_DIR})
else()
  set(GMP_LIB "")
  set(GMPXX_LIB "")
endif()

find_package(OpenMP)
set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")

install(DIRECTORY include/
  DESTINATION include
  FILES_MATCHING
  PATTERN "*.hpp"
  PATTERN "*.hh"
  PATTERN "*.h"
  PATTERN ".svn" EXCLUDE
  )

install(DIRECTORY ${CMAKE_BINARY_DIR}/include/
  DESTINATION include
  FILES_MATCHING
  PATTERN "*.hpp"
  PATTERN "*.hh"
  PATTERN "*.h"
  PATTERN "CMakeFiles" EXCLUDE
  PATTERN ".svn" EXCLUDE
  )


set(CMAKE_CXX_EXTENSIONS ON)
add_definitions(-Wno-redeclared-class-member -Wno-sometimes-uninitialized)
add_definitions(-Wno-covered-switch-default)
add_definitions(-Wno-inconsistent-missing-override)
add_definitions(-Wno-deprecated-declarations)
if ("${CMAKE_CXX_COMPILER_ID}" MATCHES "GNU")
  add_definitions( -Wno-unused-local-typedefs)
endif ()

# add the include directory from the build tree
include_directories(BEFORE ${CMAKE_CURRENT_BINARY_DIR}/include)

if (IS_DIRECTORY ${CMAKE_SOURCE_DIR}/llvm-dsa AND
    EXISTS ${CMAKE_SOURCE_DIR}/llvm-dsa/lib/DSA/Steensgaard.cpp)
  include_directories (AFTER llvm-dsa/include)
  add_subdirectory (llvm-dsa/lib/AssistDS)
  add_subdirectory (llvm-dsa/lib/DSA)
  set (DSA_LIBS DSA AssistDS)
  set (HAVE_DSA TRUE)
else()
  message (WARNING "No LLVM DSA found in ${CMAKE_SOURCE_DIR}/llvm-dsa. Run\n\tcmake --build . --target extra && cmake ${CMAKE_SOURCE_DIR}")
  set (DSA_LIBS "")
endif()

if (IS_DIRECTORY ${CMAKE_SOURCE_DIR}/llvm-seahorn AND
    EXISTS ${CMAKE_SOURCE_DIR}/llvm-seahorn/lib/CMakeLists.txt)
  include_directories (BEFORE llvm-seahorn/include)
  add_subdirectory(llvm-seahorn/lib)
  add_subdirectory(llvm-seahorn/tools)
  set (HAVE_LLVM_SEAHORN TRUE)
  set (LLVM_SEAHORN_LIBS SeaInstCombine SeaLoops)
else()
  message (WARNING "No LLVM-SEAHORN found in ${CMAKE_SOURCE_DIR}/llvm-seahorn. Run\n\tcmake --build . --target extra && cmake ${CMAKE_SOURCE_DIR}")
endif()

if (IS_DIRECTORY ${CMAKE_SOURCE_DIR}/crab-llvm AND
    EXISTS ${CMAKE_SOURCE_DIR}/crab-llvm/CMakeLists.txt)
  add_subdirectory(${CMAKE_SOURCE_DIR}/crab-llvm)
  set (HAVE_CRAB_LLVM TRUE)
  include_directories (${CRABLLVM_INCLUDE_DIRS})  
else()
  message (WARNING "No CRAB-LLVM found in ${CMAKE_SOURCE_DIR}/crab-llvm. Run\n\tcmake --build . --target extra && cmake ${CMAKE_SOURCE_DIR}")
endif()

if (IS_DIRECTORY ${CMAKE_SOURCE_DIR}/sea-dsa AND
    EXISTS ${CMAKE_SOURCE_DIR}/sea-dsa/src/DsaAnalysis.cc)
  include_directories (AFTER sea-dsa/include)
  add_subdirectory (${CMAKE_SOURCE_DIR}/sea-dsa)
  set (SEA_DSA_LIBS SeaDsaAnalysis)
else()
  message (WARNING "No SEA DSA found in ${CMAKE_SOURCE_DIR}/sea-dsa. Run\n\tcmake --build . --target extra && cmake ${CMAKE_SOURCE_DIR}")
  return()
endif()

### add our include directories to the front, overriding directories
### specified by external packages.
include_directories(BEFORE
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/include)


add_subdirectory(lib)
add_subdirectory(tools)
if (UNIT_TESTS)
  add_subdirectory(units)
endif()
add_subdirectory(sea-rt)

configure_file( include/seahorn/config.h.cmake
                ${CMAKE_BINARY_DIR}/include/seahorn/config.h )

add_subdirectory(py)
add_subdirectory(test)
