add_llvm_library (seahorn.LIB
  LoadIkos.cc
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
if (HAVE_IKOS_LLVM)
  target_link_libraries (seahorn.LIB LlvmIkosPasses)
endif()

set_target_properties (seahorn.LIB PROPERTIES OUTPUT_NAME "seahorn")

add_llvm_library(seabmc.LIB
  SymStore.cc
  LiveSymbols.cc
  SymExec.cc
  UfoSymExec.cc
  BMCFunction.cc
  BMCModule.cc
  ZOption.cc
  )

set_target_properties (seahorn.LIB PROPERTIES OUTPUT_NAME "seabmc")
