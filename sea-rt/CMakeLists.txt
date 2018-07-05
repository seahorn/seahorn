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
