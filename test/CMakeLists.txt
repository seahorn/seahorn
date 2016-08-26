# find lit. Assume we are using external lit installed from pip
find_program(LIT_COMMAND lit)

# add the test suite
add_lit_testsuite(test-simple "Run simple tests"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/simple
  PARAMS
  test_dir=${CMAKE_CURRENT_BINARY_DIR}
  sea_cmd="${PROJECT_BINARY_DIR}/run/bin/sea"
  DEPENDS seahorn
  )

add_lit_testsuite(pred-abs "Regression test on Predicate Abstraction"
   -v
   ${CMAKE_CURRENT_SOURCE_DIR}/predabs
   PARAMS
   test_dir=${CMAKE_CURRENT_BINARY_DIR}
   sea_cmd="${PROJECT_BINARY_DIR}/run/bin/sea"
   DEPENDS seahorn
   )

add_lit_testsuite(test-solve "Regression test on Predicate Abstraction"
   -v
   ${CMAKE_CURRENT_SOURCE_DIR}/solve
   PARAMS
   test_dir=${CMAKE_CURRENT_BINARY_DIR}
   sea_cmd="${PROJECT_BINARY_DIR}/run/bin/sea"
   DEPENDS seahorn
   )
