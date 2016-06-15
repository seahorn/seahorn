add_library(sea-rt
  seahorn.c)

install (TARGETS sea-rt
  LIBRARY DESTINATION lib
  ARCHIVE DESTINATION lib)
