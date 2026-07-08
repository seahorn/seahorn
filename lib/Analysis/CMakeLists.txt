add_llvm_library (SeaAnalysis DISABLE_LLVM_LINK_LLVM_DYLIB
  CanFail.cc
  SeaNewPmAnalyses.cc
  CrabAnalysis.cc  
  CutPointGraph.cc
  TopologicalOrder.cc
  CanReadUndef.cc
  GateAnalysis.cc
  ControlDependenceAnalysis.cc
  ClassHierarchyAnalysis.cc
  SeaBuiltinsInfo.cc
  )

if (HAVE_CLAM)
  target_link_libraries (SeaAnalysis PRIVATE ${CLAM_LIBS})
endif()
