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
  PathBmc.cc
  PathBmcBoolAbs.cc  
  PathBmcMuc.cc
  PathBmcTrace.cc
  PathBmcUtil.cc  
  Bmc.cc
  BmcPass.cc
  BvOpSem.cc
  # BvInt.cc
  MemSimulator.cc
  ZOption.cc
  BoogieWriter.cc
  BvOpSem2.cc
  BvOpSem2Mem.cc
  BvOpSem2MemRepr.cc
  BvOpSem2MemManager.cc
  BvOpSem2Allocators.cc
  BvOpSem2Alu.cc
  BvOpSem2ConstEval.cc
  VCGen.cc
  DfCoiAnalysis.cc
  )

add_subdirectory(Smt)
if (HAVE_CLAM)
  target_link_libraries (seahorn.LIB ${CLAM_LIBS})
endif()


set_target_properties (seahorn.LIB PROPERTIES OUTPUT_NAME "seahorn")
