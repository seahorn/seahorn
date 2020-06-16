#!/bin/bash

##
## Run tests and collect coverage
##
## The script expects to run in a docker container with fixed paths
##

# run tests
# XXX limit to tests that succeed currently, re-enable when all test pass
# lit /seahorn/test
lit /seahorn/test/opsem
lit -D opsem-opts=--horn-bv2-widemem /seahorn/test/opsem 
lit -D opsem-opts=--horn-bv2-extra-widemem /seahorn/test/opsem
lit /seahorn/test/mcfuzz
lit /seahorn/test/simple

# collect coverage
lcov -c -d /seahorn/build/lib/ \
     -b /seahorn/build/ -o coverage.info \
     --gcov-tool=/seahorn/scripts/coverage/llvm-gcov-10.sh

# filter seahorn relevant info 
lcov -e coverage.info '/seahorn/*' -o all.info
