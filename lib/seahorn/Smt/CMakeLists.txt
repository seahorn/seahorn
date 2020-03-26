add_library (SeaSmt
  MarshalYices.cc
  Yices2SolverImpl.cc
  Yices2ModelImpl.cc
  ExprToZ.cc
  ZToExpr.cc
  ExprUtil.cc
  )

target_link_libraries(SeaSmt ${Z3_LIBRARY})

if (YICES2_FOUND)
  target_link_libraries(SeaSmt ${YICES2_LIBRARY})
endif()

