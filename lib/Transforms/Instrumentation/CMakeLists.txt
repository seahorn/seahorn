add_llvm_library(SeaInstrumentation DISABLE_LLVM_LINK_LLVM_DYLIB 
  MixedSemantics.cc
  NondetInit.cc
  MarkFnEntry.cc
  EnumVerifierCalls.cc
  StripLifetime.cc
  StripUselessDeclarations.cc
  KleeInternalize.cc
  WrapMem.cc
  RenameNondet.cc
  NullCheck.cc
  SimpleMemoryCheck.cc
  FatBufferBoundsCheck.cc
  BranchSentinelPass.cc
  GeneratePartialFnPass.cc
  CrabAnalysis.cc
  )

if (HAVE_CLAM)
  target_link_libraries (SeaInstrumentation PRIVATE ${CLAM_LIBS})
endif()