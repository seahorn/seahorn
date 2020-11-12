cmake_minimum_required(VERSION 3.10.2)

project (SeaHorn)
set (SeaHorn_VERSION_MAJOR 10)
set (SeaHorn_VERSION_MINOR 0)
set (SeaHorn_VERSION_PATCH 0)
set (SeaHorn_VERSION_TWEAK "rc0")

if(CMAKE_VERSION VERSION_GREATER "3.13.0")
cmake_policy(SET CMP0074 NEW)
cmake_policy(SET CMP0077 NEW)
endif()

set(CMAKE_CXX_STANDARD 14 CACHE STRING "C++ standard to conform to")
set(CMAKE_CXX_STANDARD_REQUIRED YES)
set(CMAKE_CXX_EXTENSIONS NO)

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

# Default is release with debug info
if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE RelWithDebInfo CACHE STRING
    "Choose the type of build, options are: None Debug Release RelWithDebInfo MinSizeRel." FORCE)
endif()

option(SEA_ENABLE_LLD "Use lld as C and C++ linker." OFF)
if(SEA_ENABLE_LLD) 
  set(CMAKE_EXE_LINKER_FLAGS "-fuse-ld=lld")
endif()

option(SEA_USE_SPLIT_DWARF "Use -gsplit-dwarf. Decreases linker pressure." OFF)

option(SEA_ENABLE_ASSERTIONS "Enable assertions." OFF)

# Add path for custom modules
list (APPEND CMAKE_MODULE_PATH
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake")

# Configuration for Coverage
if (CMAKE_BUILD_TYPE STREQUAL Coverage)
  include(Coverage)
  # We don't want coverage on external things
  set(EXT_CMAKE_BUILD_TYPE Release)
else()
  set(EXT_CMAKE_BUILD_TYPE ${CMAKE_BUILD_TYPE})
endif ()

# Getting git SHA-1
list(APPEND CMAKE_MODULE_PATH 
  "${CMAKE_CURRENT_SOURCE_DIR}/cmake/getGitRevisionModule/")

include(GetGitRevisionDescription)
get_git_head_revision(GIT_REFSPEC GIT_SHA1)

configure_file("${CMAKE_CURRENT_SOURCE_DIR}/lib/Support/GitSHA1.cc.in" "${CMAKE_CURRENT_SOURCE_DIR}/lib/Support/GitSHA1.cc" @ONLY)

find_package (Git)
if (GIT_FOUND)
  set (SEAHORN_LLVM_REPO "https://github.com/seahorn/llvm-seahorn"
    CACHE STRING "llvm-seahorn repo")
  set (SEA_DSA_REPO "https://github.com/seahorn/sea-dsa"
    CACHE STRING "sea-dsa repo")
  set (CLAM_REPO "https://github.com/seahorn/crab-llvm"
    CACHE STRING "clam repo")
  
  add_custom_target (llvm-seahorn-git
    ${GIT_EXECUTABLE} clone ${SEAHORN_LLVM_REPO} ${CMAKE_SOURCE_DIR}/llvm-seahorn -b dev10)
  add_custom_target (sea-dsa-git
    ${GIT_EXECUTABLE} clone ${SEA_DSA_REPO} ${CMAKE_SOURCE_DIR}/sea-dsa -b dev10)
  add_custom_target (clam-git
    ${GIT_EXECUTABLE} clone ${CLAM_REPO} ${CMAKE_SOURCE_DIR}/clam -b dev10)
  add_custom_target (extra
    ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
    DEPENDS
    sea-dsa-git    
    llvm-seahorn-git
    clam-git
  )

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

set(CMAKE_INSTALL_RPATH_USE_LINK_PATH TRUE)
if(${CMAKE_SYSTEM_NAME} MATCHES "Darwin")
  set(CMAKE_MACOSX_RPATH TRUE)  
  set(CMAKE_INSTALL_RPATH "@loader_path/../lib")
elseif(${CMAKE_SYSTEM_NAME} MATCHES "Linux")
  set(CMAKE_INSTALL_RPATH "\$ORIGIN/../lib")
else()
  set(CMAKE_INSTALL_RPATH "${CMAKE_INSTALL_PREFIX}/lib")
endif ()


include(ExternalProject)
set_property(DIRECTORY PROPERTY EP_STEP_TARGETS configure build test)
set (Z3_TAG "origin/deep_space" CACHE STRING "Z3 git tag to use")
set (Z3_REPO "https://github.com/agurfinkel/z3.git" CACHE STRING "Z3 repo")
ExternalProject_Add(z3
  GIT_REPOSITORY  ${Z3_REPO}
  GIT_TAG ${Z3_TAG}
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CMAKE_ARGS
  -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER}
  -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
  -DCMAKE_LINKER=${CMAKE_LINKER}
  -DCMAKE_BUILD_TYPE:STRING=${EXT_CMAKE_BUILD_TYPE}
  -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>
  -DBUILD_LIBZ3_SHARED:BOOL=FALSE  
  TEST_AFTER_INSTALL 1
  TEST_COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_INSTALL 1
  LOG_BUILD 1)

find_package(Z3 4.8.7)
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


# Find Yices
SET(YICES2_HOME CACHE STRING "Yices2 installation directory")
find_package(Yices2 2.6.0)
if (YICES2_FOUND)
  add_definitions(-DWITH_YICES2)
  include_directories(${YICES2_INCLUDE_DIR})
  message("Found Yices2 at ${YICES2_HOME}")
  install(PROGRAMS ${YICES2_EXECUTABLE} DESTINATION bin)
  if (YICES2_HOME)
    file(GLOB _YICES2_LIBRARIES ${YICES2_HOME}/lib/* *.dylib *.so *.a)
    install(FILES ${_YICES2_LIBRARIES} DESTINATION lib)
  else()
    # this may copy only the symbolic link
    install(FILES ${YICES2_LIBRARY} DESTINATION lib)
  endif()
endif()  

# if top-level, offer to build llvm
ExternalProject_Add (llvm
  SVN_REPOSITORY http://llvm.org/svn/llvm-project/llvm/tags/RELEASE_800/final/
  SOURCE_DIR ${CMAKE_SOURCE_DIR}/ext/llvm
  INSTALL_DIR ${CMAKE_BINARY_DIR}/run
  CMAKE_ARGS
  -DCMAKE_C_COMPILER=${CMAKE_C_COMPILER} -DCMAKE_CXX_COMPILER=${CMAKE_CXX_COMPILER}
  -DCMAKE_BUILD_TYPE:STRING=${EXT_CMAKE_BUILD_TYPE}
  -DCMAKE_INSTALL_PREFIX:PATH=<INSTALL_DIR>
  -DLLVM_TARGETS_TO_BUILD:STRING=X86 -DWITH_POLY:BOOL=OFF
  -DLLVM_ENABLE_PEDANTIC=OFF
  -DLLVM_ENABLE_LLD=${SEA_ENABLE_LLD}
  -DLLVM_ENABLE_PIC=ON 
  -DLLVM_BUILD_LLVM_DYLIB:BOOL=${BUILD_SEA_DSA_LIBS_SHARED}
  -DLLVM_INCLUDE_TESTS:BOOL=OFF
  -DLLVM_INCLUDE_GO_TESTS=OFF
  -DLLVM_INCLUDE_EXAMPLES=OFF
  -DLLVM_INCLUDE_DOCS=OFF
  -DLLVM_BINDINGS_LIST=" "
  TEST_AFTER_INSTALL 1
  TEST_COMMAND ${CMAKE_COMMAND} -E touch ${CMAKE_CURRENT_LIST_FILE}
  LOG_CONFIGURE 1
  LOG_BUILD 1
  LOG_INSTALL 1)

find_package (LLVM 10 CONFIG)
if (NOT LLVM_FOUND)
  ExternalProject_Get_Property (llvm INSTALL_DIR)
  set (LLVM_ROOT ${INSTALL_DIR})
  set (LLVM_DIR ${LLVM_ROOT}/lib/cmake/llvm CACHE PATH
    "Forced location of LLVM cmake config" FORCE)
  message (WARNING "No llvm found. Run \n\tcmake --build . && cmake ${CMAKE_SOURCE_DIR}")
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

  include_directories(${LLVM_INCLUDE_DIRS})
  link_directories(${LLVM_LIBRARY_DIRS})
  add_definitions(${LLVM_DEFINITIONS})

  if (NOT LLVM_BUILD_TYPE STREQUAL CMAKE_BUILD_TYPE)
    message(WARNING
      "LLVM_BUILD_TYPE and CMAKE_BUILD_TYPE differ:\n"
      "\tLLMV_BUILD_TYPE=${LLVM_BUILD_TYPE}\n"
      "\tCMAKE_BUILD_TYPE=${CMAKE_BUILD_TYPE}\n"
      "Runtime errors might occur.")
    if (LLVM_BUILD_TYPE MATCHES "Release|RelWithDebInfo" AND 
        CMAKE_BUILD_TYPE MATCHES "Release|RelWithDebInfo|Coverage")
      message(STATUS "Assuming that mixing Release and RelWithDebInfo or Coverage is allowed.")
    else()
      message(FATAL_ERROR "Incompatible mix of LLVM_BUILD_TYPE and CMAKE_BUILD_TYPE")
    endif()
  endif()

endif()

if (NOT Z3_FOUND)
  message(WARNING "No suitable version of Z3 found.\
                   Follow instructions above.")
  return()
endif()
if(NOT LLVM_FOUND)
  message(WARNING "No suitable version of LLVM found.\
                   Follow instructions above.")
  return()
endif()

# boost version >= 1.71 because of https://github.com/boostorg/hana/issues/446
set(Boost_USE_STATIC_LIBS ${SEAHORN_STATIC_EXE})
find_package(Boost 1.71 REQUIRED)
if (Boost_FOUND)
  include_directories (${Boost_INCLUDE_DIRS})
  if(NOT LLVM_ENABLE_EH)
    add_definitions(-DBOOST_NO_EXCEPTIONS)
  endif()
endif ()



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

if (EXISTS ${CMAKE_CURRENT_BINARY_DIR}/llvm-prefix/src/llvm-build/bin/clang-5.0)
  install (
    PROGRAMS
    ${CMAKE_CURRENT_BINARY_DIR}/llvm-prefix/src/llvm-build/bin/clang-5.0
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

if (EXISTS ${CMAKE_CURRENT_SOURCE_DIR}/clam/LICENSE)
  install (FILES clam/LICENSE
    DESTINATION share/doc/seahorn
    RENAME clam_license.txt)
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
else()
  set(GMP_LIB "")
endif()

find_package(OpenMP)
if (OpenMP_FOUND OR OPENMP_FOUND)
  set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} ${OpenMP_CXX_FLAGS}")
endif()

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

# HAVE_DSA
set(DSA_LIBS "")

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

if (IS_DIRECTORY ${CMAKE_SOURCE_DIR}/sea-dsa AND
    EXISTS ${CMAKE_SOURCE_DIR}/sea-dsa/lib/seadsa/DsaAnalysis.cc)
  include_directories (BEFORE sea-dsa/include)
  add_subdirectory (${CMAKE_SOURCE_DIR}/sea-dsa)
  set (SEA_DSA_LIBS SeaDsaAnalysis)
else()
  message (WARNING "SeaDsa is required but not found in ${CMAKE_SOURCE_DIR}/sea-dsa. Run\n\tcmake --build . --target extra && cmake ${CMAKE_SOURCE_DIR}")
  return()
endif()

if (IS_DIRECTORY ${CMAKE_SOURCE_DIR}/clam AND
    EXISTS ${CMAKE_SOURCE_DIR}/clam/CMakeLists.txt)
  if (NOT CLAM_ALL_DOMAINS)
    set(CLAM_ALL_DOMAINS OFF CACHE BOOL "Include all crab abstract domains" FORCE)
  endif()
  if (NOT CLAM_ENABLE_INTER)
    set(CLAM_ENABLE_INTER OFF CACHE BOOL "Include crab inter-procedural analysis" FORCE)
  endif()
  add_subdirectory(${CMAKE_SOURCE_DIR}/clam)
  set(HAVE_CLAM TRUE)
  include_directories (BEFORE ${CLAM_INCLUDE_DIRS})
else()
  message (WARNING "No Clam found in ${CMAKE_SOURCE_DIR}/clam. Run\n\tcmake --build . --target extra && cmake ${CMAKE_SOURCE_DIR}")
endif()

# If enabled then devirtualization uses old code that replaces
# indirect calls with special bounce functions.
option(SEA_USE_BOUNCE_FUNCTIONS "Devirt uses old code that adds bounce functions" OFF)
if (SEA_USE_BOUNCE_FUNCTIONS)
  set(USE_BOUNCE_FUNCTIONS TRUE)
else()
  set(USE_BOUNCE_FUNCTIONS FALSE)
endif()

### add our include directories to the front, overriding directories
### specified by external packages.
include_directories(BEFORE
  ${CMAKE_CURRENT_SOURCE_DIR}/include
  ${CMAKE_CURRENT_BINARY_DIR}/include)


add_subdirectory(lib)
add_subdirectory(tools)
add_subdirectory(units)
add_subdirectory(sea-rt)

configure_file( include/seahorn/config.h.cmake
                ${CMAKE_BINARY_DIR}/include/seahorn/config.h )

add_subdirectory(py)
add_subdirectory(test)
