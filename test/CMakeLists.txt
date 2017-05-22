# find lit. Assume we are using external lit installed from pip
find_program(LIT_COMMAND lit)

# add the test suite
add_lit_testsuite(test-simple "Run simple tests"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/simple
  PARAMS
  test_dir=${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS seahorn
  )

add_lit_testsuite(test-solve "Run more tests"
   -v
   ${CMAKE_CURRENT_SOURCE_DIR}/solve
   PARAMS
   test_dir=${CMAKE_CURRENT_BINARY_DIR}
   DEPENDS seahorn
   )

add_lit_testsuite(pred-abs "Regression test on Predicate Abstraction"
   -v
   ${CMAKE_CURRENT_SOURCE_DIR}/predabs
   PARAMS
   test_dir=${CMAKE_CURRENT_BINARY_DIR}
   DEPENDS seahorn
   )

add_lit_testsuite(test-abc "Regression test for Array Bounds Checks"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/abc
  PARAMS
  test_dir=${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS seahorn
  )

add_lit_testsuite(test-inc "Regression test for Inconsistency Analysis"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/inc
  PARAMS
  test_dir=${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS seahorn
  )

add_lit_testsuite(test-dsa "Regression test for DSA"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/dsa
  PARAMS
  test_dir=${CMAKE_CURRENT_BINARY_DIR}
  DEPENDS seahorn
  )
