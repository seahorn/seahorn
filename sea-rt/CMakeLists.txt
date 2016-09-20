add_library(sea-rt
  seahorn.cpp)

install (TARGETS sea-rt
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib)
