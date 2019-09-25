#!/bin/bash
apt update && apt install -y lcov ggcov && \
cd /seahorn/build && cmake --build . --target test-opsem && \
lcov -c --directory /seahorn/build/lib/seahorn/CMakeFiles/seahorn.LIB.dir/ -o coverage.info && \
lcov --extract coverage.info */lib/seahorn/* -o lib.info && \
lcov --extract coverage.info */include/seahorn/* -o header.info && \
cat header.info lib.info > all.info && \
bash <(curl -s https://codecov.io/bash) -f all.info
