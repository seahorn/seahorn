#!/bin/bash
cd /seahorn/build && cmake --build . --target test-all
lcov -c --directory /seahorn/build/lib/seahorn/CMakeFiles/seahorn.LIB.dir/ -o coverage.info
lcov --extract coverage.info */lib/seahorn/* -o lib.info
lcov --extract coverage.info */include/seahorn/* -o header.info
cat header.info lib.info > all.info
