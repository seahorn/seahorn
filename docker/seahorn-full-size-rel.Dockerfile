#
# Dockerfile for SeaHorn binary
# produces package in /seahorn/build
# Arguments:
#  - UBUNTU:     trusty, xenial
#  - BUILD_TYPE: debug, release
#  - TRAVIS:     true (optional, for use on Travis only)
#

ARG UBUNTU

# Pull base image.
FROM seahorn/seahorn-build:$UBUNTU

ARG TRAVIS

# clone SeaHorn (just copy on Travis)
COPY . /seahorn
RUN if [ "$TRAVIS" != "true" ] ; \
      then rm -rf /seahorn/seahorn && git clone https://github.com/seahorn/seahorn -b master --depth=10 ; \
    fi && \
    mkdir -p /seahorn/build
WORKDIR /seahorn/build

ARG BUILD_TYPE

# Build configuration.
RUN cmake -GNinja \
          -DCMAKE_BUILD_TYPE=$BUILD_TYPE \ 
          -DBOOST_ROOT=/deps/boost \
          -DZ3_ROOT=/deps/z3 \
          -DLLVM_DIR=/deps/LLVM-3.8.1-Linux/share/llvm/cmake \
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
    ln -s /clang-3.8/bin/clang run/bin/clang && \
    ln -s /clang-3.8/bin/clang++ run/bin/clang++

ENV PATH "/seahorn/build/run/bin:$PATH"

WORKDIR /seahorn
