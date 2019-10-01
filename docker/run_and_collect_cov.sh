#!/bin/bash
lit /seahorn/test
lcov -c -d /seahorn/build/lib/ -b /seahorn/build/ -o coverage.info
lcov -e coverage.info '/seahorn/lib/*' '/seahorn/include/*' -o all.info
