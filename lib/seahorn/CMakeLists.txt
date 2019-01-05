add_llvm_library (seahorn.LIB
  LoadCrab.cc
  LiveSymbols.cc
  SymStore.cc
  UfoOpSem.cc
  ClpOpSem.cc
  HornifyModule.cc
  HornifyFunction.cc
  FlatHornifyFunction.cc
  IncHornifyFunction.cc
  HornWrite.cc
  HornSolver.cc
  Houdini.cc
  HornModelConverter.cc
  HornDbModel.cc
  PredicateAbstraction.cc
  GuessCandidates.cc
  HornCex.cc
  CexHarness.cc
  ClpWrite.cc
  HornClauseDB.cc
  HornClauseDBTransf.cc
  PathBasedBmc.cc
  Bmc.cc    
  BmcPass.cc
  BvOpSem.cc
  # BvInt.cc
  MemSimulator.cc
  ZOption.cc
  BoogieWriter.cc
  BvOpSem2.cc
  BvOpSem2Mem.cc
  VCGen.cc
  )

if (HAVE_CRAB_LLVM)
  target_link_libraries (seahorn.LIB ${CRABLLVM_LIBS})
endif()

set_target_properties (seahorn.LIB PROPERTIES OUTPUT_NAME "seahorn")

