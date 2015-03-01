
set (BASE_LIBS 
  ${Boost_UNIT_TEST_FRAMEWORK_LIBRARY} 
  ${Boost_SYSTEM_LIBRARY}
  ${GMPXX_LIB} ${GMP_LIB} ${RT_LIB} ncurses dl)

add_executable (fapp_z3 fapp_z3.cpp)
target_link_libraries (fapp_z3 ${Z3_LIBRARY})
llvm_config (fapp_z3  instrumentation)
target_link_libraries (fapp_z3 ${BASE_LIBS})
add_test (NAME units/fapp_z3 COMMAND fapp_z3)

add_executable (muz_test muz_test.cpp)
target_link_libraries (muz_test ${Z3_LIBRARY})
llvm_config (muz_test instrumentation)
target_link_libraries (muz_test ${BASE_LIBS})
add_test (NAME units/muz_test COMMAND muz_test)

