add_llvm_library (seahorn.LIB DISABLE_LLVM_LINK_LLVM_DYLIB
  LoadCrab.cc
  LiveSymbols.cc
  SymStore.cc
  UfoOpSem.cc
  InterMemPreProc.cc
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
  FiniteMapTransf.cc
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
  BvOpSem2RawMemMgr.cc
  BvOpSem2FatMemMgr.cc
  BvOpSem2WideMemMgr.cc
  BvOpSem2ExtraWideMemMgr.cc
  VCGen.cc
  DfCoiAnalysis.cc
  )

add_subdirectory(Smt)
if (HAVE_CLAM)
  target_link_libraries (seahorn.LIB PRIVATE ${CLAM_LIBS})
endif()


set_target_properties (seahorn.LIB PROPERTIES OUTPUT_NAME "seahorn")
