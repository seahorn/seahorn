add_subdirectory(passes)
add_subdirectory(avy)
add_subdirectory(seahorn)

add_llvm_loadable_module (shadow 
  passes/ShadowMemDsa.cc 
  passes/NondetInit.cc
  passes/PromoteVerifierCalls.cc
  passes/LowerGvInitializers.cc
  passes/CanFail.cc
  passes/MixedSemantics.cc
  passes/Local.cc
  passes/LoopUnhoist.cc
  )

target_link_libraries (shadow avy)
if (HAVE_DSA)
  target_link_libraries (shadow ${DSA_LIBS})
endif()
install (TARGETS shadow LIBRARY DESTINATION lib)

add_llvm_loadable_module (checks
  passes/LowerCstExpr.cc
  passes/CanAccessMemory.cc
  passes/ShadowBufferBoundsCheckFuncPars.cc
  passes/BufferBoundsCheck.cc
  passes/IntegerOverflowCheck.cc
)

target_link_libraries (checks avy)
install (TARGETS checks LIBRARY DESTINATION lib)
