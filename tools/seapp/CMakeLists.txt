set (USED_LIBS 
  SeaInstrumentation
  SeaTransformsScalar
  SeaTransformsUtils
  SeaAnalysis
  ${SEA_DSA_LIBS}  
  SeaSupport
  ${LLVM_SEAHORN_LIBS}
  ${Boost_SYSTEM_LIBRARY}
  ${GMPXX_LIB}
  ${GMP_LIB}
  ${RT_LIB})

set(LLVM_LINK_COMPONENTS irreader bitwriter ipo scalaropts instrumentation core 
  # XXX not clear why these last two are required
  codegen objcarcopts)
add_llvm_executable(seapp seapp.cc)
target_link_libraries (seapp ${USED_LIBS})
llvm_config (seapp ${LLVM_LINK_COMPONENTS})
install(TARGETS seapp RUNTIME DESTINATION bin)

if (SEAHORN_STATIC_EXE)
  set (CMAKE_EXE_LINKER_FLAGS "-static -static-libgcc -static-libstdc++")
  set_target_properties (seapp PROPERTIES LINK_SEARCH_START_STATIC ON)
  set_target_properties (seapp PROPERTIES LINK_SEARCH_END_STATIC ON)
endif()
