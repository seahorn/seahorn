add_llvm_library (SeaTransformsScalar
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
  )
