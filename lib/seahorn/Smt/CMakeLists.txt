add_llvm_library (SeaSmt DISABLE_LLVM_LINK_LLVM_DYLIB
  MarshalYices.cc
  MarshalBitwuzla.cc
  BitwuzlaSolverImpl.cc
  BitwuzlaModelImpl.cc
  BitwuzlaEncodingCheck.cc
  EncodingCheck.cc
  Yices2SolverImpl.cc
  Yices2ModelImpl.cc
  ExprToZ.cc
  ZToExpr.cc
  ZToExprNoRec.cc
  ExprUtil.cc
  TypeChecker.cc
  HexDump.cc
  ExprMemMap.cc
  )

target_link_libraries(SeaSmt PRIVATE ${Z3_LIBRARY})

if (YICES2_FOUND)
  target_link_libraries(SeaSmt PRIVATE ${YICES2_LIBRARY})
endif()

if (BITWUZLA_FOUND)
  target_link_libraries(SeaSmt PRIVATE ${BITWUZLA_LIBRARY})
endif()

# Bitwuzla reports errors with C++ exceptions. LLVM, and so SeaHorn, may be
# built with -fno-exceptions; the Bitwuzla files catch them all themselves.
# EncodingCheck.cc is not among them: it includes z3++.h, which must be
# compiled the same way as in the rest of SeaHorn.
set_source_files_properties(MarshalBitwuzla.cc BitwuzlaSolverImpl.cc
  BitwuzlaModelImpl.cc BitwuzlaEncodingCheck.cc
  PROPERTIES COMPILE_FLAGS -fexceptions)

