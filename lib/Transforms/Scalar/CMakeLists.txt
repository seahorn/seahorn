add_llvm_library (SeaTransformsScalar DISABLE_LLVM_LINK_LLVM_DYLIB
  LoopUnhoist.cc
  LowerCstExpr.cc
  LowerGvInitializers.cc
  LowerArithInstrinsics.cc
  LowerLibCxxAbiFunctions.cc
  PromoteVerifierCalls.cc
  CutLoops.cc
  PromoteMalloc.cc
  KillVarArgFn.cc
  PromoteBoolLoads.cc
  SimplifyPointerLoops.cc
  SymbolizeConstantLoopBounds.cc
  LowerAssert.cc
  UnfoldLoopForDsa.cc
  PromoteSeahornAssume.cc
  PromoteMemcpy.cc
  UnifyAssumes.cc
  LoopPeeler.cc
  BackedgeCutter.cc
  LowerIsDeref.cc
  CrabLowerIsDeref.cc
  )

# if (HAVE_CLAM)
#   target_link_libraries (SeaTransformsScalar PRIVATE ${CLAM_LIBS})
# endif()
