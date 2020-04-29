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
  )
