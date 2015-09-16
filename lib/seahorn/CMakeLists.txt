add_llvm_library (seahorn.LIB 
  LoadCrab.cc
  LiveSymbols.cc 
  SymStore.cc
  SymExec.cc
  UfoSymExec.cc
  ClpSymExec.cc
  HornifyModule.cc 
  HornifyFunction.cc 
  FlatHornifyFunction.cc
  HornWrite.cc
  HornSolver.cc
  HornCex.cc
  ClpWrite.cc
  HornClauseDB.cc
  HornClauseDBTransf.cc
  ZOption.cc
  )

# no need to link with static libraries
if (HAVE_CRAB_LLVM)
  target_link_libraries (seahorn.LIB CrabLlvmAnalysis CrabLlvmInstrumentation)
endif()

set_target_properties (seahorn.LIB PROPERTIES OUTPUT_NAME "seahorn")
