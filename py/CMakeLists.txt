find_program(PYTHON python3 REQUIRED)

set (SRC
  sea/__init__.py
  sea/__main__.py
  sea/commands.py
  sea/yama.py
  )


if (PYTHON)
  install (DIRECTORY sea DESTINATION lib/seapy
    FILES_MATCHING PATTERN "*.py")
  install (DIRECTORY term DESTINATION lib/seapy
    FILES_MATCHING PATTERN "*.py")
  install (DIRECTORY inc DESTINATION lib/seapy
    FILES_MATCHING PATTERN "*.py")
  install (PROGRAMS seapy DESTINATION bin RENAME sea)

  install (FILES stats.py DESTINATION bin)
  set (Z3_SMT2 ${CMAKE_BINARY_DIR}/z3-prefix/src/z3/stats/scripts/z3_smt2.py)
  if (EXISTS ${Z3_SMT2})
    install (PROGRAMS ${Z3_SMT2} DESTINATION bin RENAME spacer)
  endif()
endif()

