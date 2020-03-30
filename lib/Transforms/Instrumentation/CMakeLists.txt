add_llvm_library(SeaInstrumentation
  MixedSemantics.cc
  NondetInit.cc
  LlvmDsaShadowMem.cc
  MarkFnEntry.cc
  EnumVerifierCalls.cc
  StripLifetime.cc
  StripUselessDeclarations.cc
  KleeInternalize.cc
  WrapMem.cc
  RenameNondet.cc
  NullCheck.cc
  BufferBoundsCheck.cc
  SimpleMemoryCheck.cc
  FatBufferBoundsCheck.cc
  )

if (HAVE_DSA)
   target_link_libraries (SeaInstrumentation ${DSA_LIBS})
endif()
target_link_libraries (SeaInstrumentation ${SEA_DSA_LIBS})
