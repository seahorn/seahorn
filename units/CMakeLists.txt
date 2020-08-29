enable_testing()
include (CTest)

# In the future we can group tests by linking dependencies and move them into
# seperate directories.
set (USED_LIBS_Z3_TESTS
  SeaSmt
  SeaSupport
  ${SEA_DSA_LIBS}
  ${LLVM_SEAHORN_LIBS}
  ${Boost_SYSTEM_LIBRARY}
  ${GMP_LIB}
  ${RT_LIB}
  )

set(LLVM_LINK_COMPONENTS irreader bitwriter ipo scalaropts instrumentation core
    # XXX not clear why these last two are required
    codegen objcarcopts)

add_executable(fp_units EXCLUDE_FROM_ALL fp_units.cc)
target_link_libraries(fp_units PRIVATE seahorn.LIB ${USED_LIBS_Z3_TESTS} )
llvm_config (fp_units ${LLVM_LINK_COMPONENTS})
add_custom_target(test_fp fp_units DEPENDS fp_units)
add_test(NAME Fp_Tests COMMAND fp_units)

add_executable(units_z3 EXCLUDE_FROM_ALL
  units_z3.cpp
  fapp_z3.cpp
  muz_test.cpp
  lambdas_z3.cpp
  units_expr.cpp
  )
llvm_config (units_z3 ${LLVM_LINK_COMPONENTS})
target_link_libraries(units_z3 PRIVATE ${USED_LIBS_Z3_TESTS})
add_custom_target(test_z3 units_z3 DEPENDS units_z3)
add_test(NAME Z3_SPACER_Tests COMMAND units_z3)


add_executable(units_yices2 EXCLUDE_FROM_ALL
  units_z3.cpp ## should be renamed
  units_yices2.cpp)
llvm_config(units_yices2 ${LLVM_LINK_COMPONENTS})
target_link_libraries(units_yices2 PRIVATE ${USED_LIBS_Z3_TESTS} SeaSmt)
add_custom_target(test_yices2 units_yices2 DEPENDS units_yices2)
add_test(NAME Smt_Solver_Tests COMMAND units_yices2)

add_executable(units_type_checker EXCLUDE_FROM_ALL TypeCheckerTests.cpp)
llvm_config(units_type_checker ${LLVM_LINK_COMPONENTS})
target_link_libraries(units_type_checker PRIVATE ${USED_LIBS_Z3_TESTS})
add_custom_target(test_type_checker units_type_checker DEPENDS units_type_checker)
add_test(NAME Type_Checker_Tests COMMAND units_type_checker)


add_executable(units_finite_map EXCLUDE_FROM_ALL units_finite_maps.cpp)
llvm_config(units_finite_map ${LLVM_LINK_COMPONENTS})
target_link_libraries(units_finite_map PRIVATE seahorn.LIB ${USED_LIBS_Z3_TESTS})
add_custom_target(test_finite_map units_finite_map DEPENDS units_finite_map)
add_test(NAME Finite_Maps_Tests COMMAND units_finite_map)

add_executable(units_hex_dump EXCLUDE_FROM_ALL HexDumpTests.cpp)
llvm_config(units_hex_dump ${LLVM_LINK_COMPONENTS})
target_link_libraries(units_hex_dump PRIVATE ${USED_LIBS_Z3_TESTS})
add_custom_target(test_hex_dump units_hex_dump DEPENDS units_hex_dump)
add_test(NAME Hex_Dump_Tests COMMAND units_hex_dump)

add_executable(units_evaluate EXCLUDE_FROM_ALL EvaluateTests.cpp)
llvm_config(units_evaluate ${LLVM_LINK_COMPONENTS})
target_link_libraries(units_evaluate PRIVATE ${USED_LIBS_Z3_TESTS})
add_custom_target(test_evaluate units_evaluate DEPENDS units_evaluate)
add_test(NAME Evaluate_Tests COMMAND units_evaluate)
