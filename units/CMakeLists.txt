enable_testing()
include (CTest)

# In the future we can group tests by linking dependencies and move them into
# seperate directories.
set (USED_LIBS_Z3_TESTS
  ${Boost_SYSTEM_LIBRARY}
  ${Z3_LIBRARY}
  ${SEA_DSA_LIBS}
  SeaSupport
  ${LLVM_SEAHORN_LIBS}
  ${GMPXX_LIB}
  ${GMP_LIB}
  ${RT_LIB}
  )

set(LLVM_LINK_COMPONENTS irreader bitwriter ipo scalaropts instrumentation core
    # XXX not clear why these last two are required
    codegen objcarcopts)

add_executable(units_z3 EXCLUDE_FROM_ALL
  units_z3.cpp
  fapp_z3.cpp
  muz_test.cpp
  )
llvm_config (units_z3 ${LLVM_LINK_COMPONENTS})

target_link_libraries(units_z3 ${USED_LIBS_Z3_TESTS})
add_custom_target(test_z3 units_z3 DEPENDS units_z3)
add_test(NAME Z3_SPACER_Tests COMMAND units_z3)
