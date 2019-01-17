# find lit. Assume we are using external lit installed from pip
find_program(LIT_COMMAND lit)

# add the test suite
add_lit_testsuite(test-all "Run all the tests"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-simple "Run simple tests"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/simple
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-solve "Run more tests"
   -v
   ${CMAKE_CURRENT_SOURCE_DIR}/solve
   ARGS
   --path=${CMAKE_INSTALL_PREFIX}/bin
   DEPENDS seahorn
   )

add_lit_testsuite(pred-abs "Regression test on Predicate Abstraction"
   -v
   ${CMAKE_CURRENT_SOURCE_DIR}/predabs
   ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
   DEPENDS seahorn
   )

add_lit_testsuite(test-abc "Regression test for Array Bounds Checks"
  #--show-tests
  ${CMAKE_CURRENT_SOURCE_DIR}/abc
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-smc "Regression test for Simple Memory Safety Checks"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/smc
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-opsem "Regression test for Operational Semantics"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/opsem
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn 
  )

add_lit_testsuite(test-inc "Regression test for Inconsistency Analysis"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/inc
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-dsa "Regression test for DSA"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/dsa
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-tutorial "Regression tests for the SeaHorn tutorial"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/tutorial
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-bmc "Regression tests for BMC"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/bmc
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-gsa "Regression tests for Gated SSA"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/gsa
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-formats "Regression test for external formats"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/formats
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

add_lit_testsuite(test-devirt "Regression test for devirtualization of functions"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/devirt
  ARGS
  --path=${CMAKE_INSTALL_PREFIX}/bin
  DEPENDS seahorn
  )

if (CMAKE_GENERATOR STREQUAL "Ninja")
  # Depending on install target does not work with make
  add_dependencies(test-all install)
  add_dependencies(test-opsem install)
  add_dependencies(test-tutorial install)
  add_dependencies(test-dsa install)
  add_dependencies(test-formats install)
  add_dependencies(test-gsa install)
  add_dependencies(test-bmc install)
  add_dependencies(test-simple install)
  add_dependencies(test-solve install)
  add_dependencies(pred-abs install)
  add_dependencies(test-abc install)
  add_dependencies(test-smc install)
  add_dependencies(test-inc install)
  add_dependencies(test-devirt install)  
endif()
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/simple DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/solve DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/smc DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/opsem DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/abc DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/bmc DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/gsa DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/devirt DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/dsa DESTINATION share/seahorn/test
  PATTERN "*/check_graphs.py" EXCLUDE
  )
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tutorial DESTINATION share/seahorn/test
  PATTERN "*/seatest.py" EXCLUDE
  )
install (FILES ${CMAKE_CURRENT_SOURCE_DIR}/lit.cfg DESTINATION share/seahorn/test)
install (PROGRAMS ${CMAKE_CURRENT_SOURCE_DIR}/dsa/check_graphs.py DESTINATION share/seahorn/test/dsa)
install (PROGRAMS ${CMAKE_CURRENT_SOURCE_DIR}/tutorial/seatest.py DESTINATION share/seahorn/test/tutorial)
