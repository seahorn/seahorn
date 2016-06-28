add_llvm_library (SeaAnalysis
  CanAccessMemory.cc
  CanFail.cc
  CutPointGraph.cc
  TopologicalOrder.cc
  CanReadUndef.cc)

add_subdirectory(DSA)
