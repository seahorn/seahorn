# based on http://bloerg.net/2012/11/10/cmake-and-distutils.html

find_program(PYTHON "python")

set (SRC
  sea/__init__.py
  sea/__main__.py
  sea/commands.py
  )


option (USE_PY_SETUP "Use python distutils to install python modules" OFF)

if (PYTHON AND NOT USE_PY_SETUP)
  install (DIRECTORY sea DESTINATION lib/seapy
    FILES_MATCHING PATTERN "*.py")
  install (DIRECTORY term DESTINATION lib/seapy
    FILES_MATCHING PATTERN "*.py")
    install (DIRECTORY inc DESTINATION lib/seapy
            FILES_MATCHING PATTERN "*.py")
  install (PROGRAMS seapy DESTINATION bin RENAME sea)
  install (PROGRAMS sea/abc.py DESTINATION bin RENAME sea_abc)
  install (PROGRAMS sea_par.py DESTINATION bin RENAME sea_svcomp)
  install (PROGRAMS inc_looper.py DESTINATION bin RENAME sea_inc)
  install (FILES seahorn-benchexec-wrapper.py DESTINATION bin)

  install (FILES stats.py DESTINATION bin)
  set (Z3_SMT2 ${CMAKE_BINARY_DIR}/z3-prefix/src/z3/stats/scripts/z3_smt2.py)
  if (EXISTS ${Z3_SMT2})
    install (PROGRAMS ${Z3_SMT2} DESTINATION bin RENAME spacer)
  endif()
endif()

if (PYTHON AND USE_PY_SETUP)
  set(SETUP_PY_IN "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in")
  set(SETUP_PY    "${CMAKE_CURRENT_BINARY_DIR}/setup.py")
  set(OUTPUT      "${CMAKE_CURRENT_BINARY_DIR}/build/timestamp")

  set(DEPS  ${SRC}
    stats.py
    seahorn_inter.py
    gcc_seahorn.py
    only_z3.py
    ${SETUP_PY_IN}
    )

  configure_file(${SETUP_PY_IN} ${SETUP_PY})

  add_custom_command(OUTPUT ${OUTPUT}
    COMMAND ${PYTHON} ${SETUP_PY} build
    COMMAND ${CMAKE_COMMAND} -E touch ${OUTPUT}
    DEPENDS ${DEPS})

  add_custom_target(python ALL DEPENDS ${OUTPUT})

  install(CODE "execute_process(COMMAND ${PYTHON} ${SETUP_PY} install --install-lib ${CMAKE_INSTALL_PREFIX}/bin --install-scripts ${CMAKE_INSTALL_PREFIX}/bin)")
endif()
