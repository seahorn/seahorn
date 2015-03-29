# based on http://bloerg.net/2012/11/10/cmake-and-distutils.html

find_program(PYTHON "python")

if (PYTHON)
  set(SETUP_PY_IN "${CMAKE_CURRENT_SOURCE_DIR}/setup.py.in")
  set(SETUP_PY    "${CMAKE_CURRENT_BINARY_DIR}/setup.py")
  set(OUTPUT      "${CMAKE_CURRENT_BINARY_DIR}/build/timestamp")

  set(DEPS        
    stats.py
    seahorn_inter.py
    gcc_seahorn.py
    only_z3.py
    sea/__init__.py
    sea/__main__.py
    sea/commands.py
    ${SETUP_PY_IN})
  
  configure_file(${SETUP_PY_IN} ${SETUP_PY})

  add_custom_command(OUTPUT ${OUTPUT}
    COMMAND ${PYTHON} ${SETUP_PY} build
    COMMAND ${CMAKE_COMMAND} -E touch ${OUTPUT}
    DEPENDS ${DEPS})

  add_custom_target(python ALL DEPENDS ${OUTPUT})

  install(CODE "execute_process(COMMAND ${PYTHON} ${SETUP_PY} install --install-lib ${CMAKE_INSTALL_PREFIX}/bin --install-scripts ${CMAKE_INSTALL_PREFIX}/bin)")
endif()
