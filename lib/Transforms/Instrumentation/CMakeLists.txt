add_llvm_library(SeaInstrumentation
  MixedSemantics.cc
  NondetInit.cc
  ShadowMemDsa.cc
  ShadowMemSeaDsa.cc
  MarkFnEntry.cc
  EnumVerifierCalls.cc
  StripLifetime.cc
  StripUselessDeclarations.cc
  KleeInternalize.cc
  WrapMem.cc
  RenameNondet.cc
  )

if (HAVE_DSA)
   target_link_libraries (SeaInstrumentation ${DSA_LIBS})
endif()

target_link_libraries (SeaInstrumentation SeaDsaAnalysis)
