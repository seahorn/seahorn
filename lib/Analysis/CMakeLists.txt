add_llvm_library (SeaAnalysis
  CanAccessMemory.cc
  CanFail.cc
  CutPointGraph.cc
  TopologicalOrder.cc
  WeakTopologicalOrder.cc
  ApiAnalysisPass.cc
  CanReadUndef.cc
  GateAnalysis.cc
  ControlDependenceAnalysis.cc
  ClassHierarchyAnalysis.cc
  StaticTaint.cc
  )
