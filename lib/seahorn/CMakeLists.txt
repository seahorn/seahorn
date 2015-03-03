add_llvm_library (seahorn.LIB 
  SymStore.cc SortTopo.cc LiveSymbols.cc 
  SymExec.cc UfoSymExec.cc HornifyFunction.cc 
  HornifyModule.cc 
  HornSolver.cc
  Stats.cc
  HornCex.cc
  ZOption.cc
  LoadIkos.cc
  )

# no need to link with static libraries
if (HAVE_IKOS_LLVM)
  target_link_libraries (seahorn.LIB LlvmIkosPasses)
endif()

set_target_properties (seahorn.LIB PROPERTIES OUTPUT_NAME "seahorn")
