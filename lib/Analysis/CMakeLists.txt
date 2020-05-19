add_llvm_library (SeaAnalysis DISABLE_LLVM_LINK_LLVM_DYLIB
  CanAccessMemory.cc
  CanFail.cc
  CutPointGraph.cc
  TopologicalOrder.cc
  WeakTopologicalOrder.cc
  CanReadUndef.cc
  GateAnalysis.cc
  ControlDependenceAnalysis.cc
  ClassHierarchyAnalysis.cc
  StaticTaint.cc
  SeaBuiltinsInfo.cc
  )
