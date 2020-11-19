add_llvm_library (SeaSmt DISABLE_LLVM_LINK_LLVM_DYLIB
  MarshalYices.cc
  Yices2SolverImpl.cc
  Yices2ModelImpl.cc
  ExprToZ.cc
  ZToExpr.cc
  ExprUtil.cc
  TypeChecker.cc
  HexDump.cc
  ExprMemMap.cc
  )

target_link_libraries(SeaSmt PRIVATE ${Z3_LIBRARY})

if (YICES2_FOUND)
  target_link_libraries(SeaSmt PRIVATE ${YICES2_LIBRARY})
endif()

