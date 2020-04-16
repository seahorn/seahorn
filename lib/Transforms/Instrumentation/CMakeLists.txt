add_llvm_library(SeaInstrumentation
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
  )

target_link_libraries (SeaInstrumentation PRIVATE ${SEADSA_LIBS})
