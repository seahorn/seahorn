add_llvm_library(SeaHornPasses 
  NameValues.cpp
  TopologicalOrder.cc
  CutPointGraph.cc
  ShadowMemDsa.cc
  NondetInit.cc
  PromoteVerifierCalls.cc
  HornWrite.cc
  RemoveUnreachableBlocksPass.cc
  CanFail.cc
  Local.cc
  LowerGvInitializers.cc
  LowerCstExpr.cc
  CanAccessMemory.cc
  ShadowBufferBoundsCheckFuncPars.cc
  BufferBoundsCheck.cc
  IntegerOverflowCheck.cc
  MarkInternalInline.cc
  MixedSemantics.cc
  DummyExitBlock.cc
  )

if (HAVE_DSA)
  target_link_libraries (SeaHornPasses ${DSA_LIBS})
endif()
