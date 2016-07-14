add_llvm_library(SeaInstrumentation
  BufferBoundsCheck.cc
  IntegerOverflowCheck.cc
  NullCheck.cc
  MixedSemantics.cc
  NondetInit.cc
  ShadowMemDsa.cc
  MarkFnEntry.cc
  EnumVerifierCalls.cc
  StripLifetime.cc
  StripUselessDeclarations.cc
  KleeInternalize.cc
  WrapMem.cc
  )
if (HAVE_DSA)
  target_link_libraries (SeaInstrumentation ${DSA_LIBS})
endif()
