add_library(sea-rt
  seahorn.cpp)

add_library(sea-mem-rt
  seahorn_mem.cpp)


install (TARGETS sea-rt
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib)
install (TARGETS sea-mem-rt
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib)


if(CMAKE_SIZEOF_VOID_P EQUAL 8)
  add_library(sea-rt-32 EXCLUDE_FROM_ALL
    seahorn.cpp)
  set_target_properties(sea-rt-32 PROPERTIES
    COMPILE_FLAGS "-m32" LINK_FLAGS "-m32")
  add_library(sea-mem-rt-32 EXCLUDE_FROM_ALL
    seahorn_mem.cpp)
  set_target_properties(sea-mem-rt-32 PROPERTIES
    COMPILE_FLAGS "-m32" LINK_FLAGS "-m32")

  install (TARGETS sea-rt-32
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    OPTIONAL)
  install (TARGETS sea-mem-rt-32
    LIBRARY DESTINATION lib
    ARCHIVE DESTINATION lib
    OPTIONAL)
endif()


