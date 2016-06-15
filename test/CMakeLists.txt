# find lit. Assume we are using external lit installed from pip
find_program(LIT_COMMAND lit)

# add the test suite
add_lit_testsuite(test-simple "Run simple tests"
  -v
  ${CMAKE_CURRENT_SOURCE_DIR}/simple
  PARAMS
  test_dir=${CMAKE_CURRENT_BINARY_DIR}
  sea_cmd="${PROJECT_BINARY_DIR}/run/bin/sea"
  sea_share="${PROJECT_BINARY_DIR}/run/share"
  DEPENDS seahorn
  )
