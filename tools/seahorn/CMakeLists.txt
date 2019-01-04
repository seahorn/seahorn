set (USED_LIBS 
  seahorn.LIB
  SeaInstrumentation
  SeaTransformsScalar
  SeaTransformsUtils
  SeaAnalysis
  ${SEA_DSA_LIBS}    
  SeaSupport
  ${LLVM_SEAHORN_LIBS}
  ${Z3_LIBRARY}
  ${Boost_SYSTEM_LIBRARY}
  ${GMPXX_LIB}
  ${GMP_LIB}
  ${RT_LIB}
  )


set(LLVM_LINK_COMPONENTS bitwriter irreader ipo scalaropts instrumentation core
  # XXX not clear why these last two are required
  codegen objcarcopts)
add_llvm_executable(seahorn seahorn.cpp)
target_link_libraries (seahorn ${USED_LIBS})
llvm_config (seahorn ${LLVM_LINK_COMPONENTS})
install(TARGETS seahorn RUNTIME DESTINATION bin)

if (SEAHORN_STATIC_EXE)
  set (CMAKE_EXE_LINKER_FLAGS "-static -static-libgcc -static-libstdc++")
  set_target_properties (seahorn PROPERTIES LINK_SEARCH_START_STATIC ON)
  set_target_properties (seahorn PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()

