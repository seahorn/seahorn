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
  -v
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

install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/simple DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/solve DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/smc DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/abc DESTINATION share/seahorn/test)
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/dsa DESTINATION share/seahorn/test
  PATTERN "*/check_graphs.py" EXCLUDE
  )
install (DIRECTORY ${CMAKE_CURRENT_SOURCE_DIR}/tutorial DESTINATION share/seahorn/test
  PATTERN "*/seatest.py" EXCLUDE
  )
install (FILES ${CMAKE_CURRENT_SOURCE_DIR}/lit.cfg DESTINATION share/seahorn/test)
install (PROGRAMS ${CMAKE_CURRENT_SOURCE_DIR}/dsa/check_graphs.py DESTINATION share/seahorn/test/dsa)
install (PROGRAMS ${CMAKE_CURRENT_SOURCE_DIR}/tutorial/seatest.py DESTINATION share/seahorn/test/tutorial)
