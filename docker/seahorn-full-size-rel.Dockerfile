#
# Dockerfile for SeaHorn binary
# produces package in /seahorn/build
# Arguments:
#  - UBUNTU:     trusty, xenial, bionic
#  - BUILD_TYPE: debug, release
#  - TRAVIS:     true (optional, for use on Travis only)
#

ARG UBUNTU

# Pull base image.
FROM seahorn/seahorn-build-llvm5:$UBUNTU

ARG TRAVIS

# clone SeaHorn (just copy on Travis)
# since there are no conditionals in docker,
# always copy, and, if needed, remove and clone instead
COPY . /seahorn
RUN if [ "$TRAVIS" != "true" ] ; \
      then cd / && rm -rf /seahorn && git clone https://github.com/seahorn/seahorn -b deep-dev-5.0 --depth=10 ; \
    fi && \
    mkdir -p /seahorn/build
WORKDIR /seahorn/build

ARG BUILD_TYPE
# Build configuration.
RUN cmake -GNinja \
          -DCMAKE_BUILD_TYPE=$BUILD_TYPE \ 
          -DBOOST_ROOT=/deps/boost \
          -DZ3_ROOT=/deps/z3 \
          -DLLVM_DIR=/deps/LLVM-5.0.2-Linux/lib/cmake/llvm \
          -DCMAKE_INSTALL_PREFIX=run \
          -DCMAKE_CXX_COMPILER=g++-5 \
          -DCPACK_GENERATOR="TGZ" \
          -DCMAKE_EXPORT_COMPILE_COMMANDS=1 \
          ../ && \
    cmake --build . --target extra  && cmake .. && \
    cmake --build . --target crab  && cmake .. && \
    cmake --build . --target install && \
    cmake --build . --target package && \
    # symlink clang (from base image)
    ln -s /clang-5.0/bin/clang run/bin/clang && \
    ln -s /clang-5.0/bin/clang++ run/bin/clang++

ENV PATH "/seahorn/build/run/bin:$PATH"

WORKDIR /seahorn
