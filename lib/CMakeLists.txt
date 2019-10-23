add_subdirectory(seahorn)
add_subdirectory(Analysis)
add_subdirectory(Transforms)
add_subdirectory(Support)

#if (HAVE_DSA)
#  target_link_libraries (shadow ${DSA_LIBS})
#endif()
#target_link_libraries (shadow ${SEA_DSA_LIBS})

#install (TARGETS shadow LIBRARY DESTINATION lib)

#add_llvm_loadable_module (checks
#  Transforms/Scalar/LowerCstExpr.cc
#  Transforms/Instrumentation/BufferBoundsCheck.cc
#  Analysis/CanAccessMemory.cc
#)

#target_link_libraries (checks avy)
#install (TARGETS checks LIBRARY DESTINATION lib)
