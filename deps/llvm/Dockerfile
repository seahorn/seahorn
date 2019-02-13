#
# llvm-5.0 Dockerfile for SeaHorn
# This produces packages in /llvm.
# Arguments:
#  - UBUNTU:     trusty, xenial
#  - BUILD_TYPE: Debug, Release, RelWithDebInfo
#

ARG UBUNTU

# Pull base image.
FROM buildpack-deps:$UBUNTU

ARG BUILD_TYPE
RUN echo "Build type set to: $BUILD_TYPE"

# Install deps.
RUN \
  apt-get update && \
  apt-get install -yqq binutils-gold cmake ninja-build

# Use gold instead of bfd for much faster linking.
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.gold" 20
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.bfd" 10

RUN mkdir -p /llvm/repo
WORKDIR /llvm/repo

# Checkout LLVM.
RUN git clone https://github.com/llvm-mirror/llvm/ ./ -b release_50 --depth=1
WORKDIR /llvm/build

# Build configuration.
RUN cmake -GNinja \
          -DCMAKE_BUILD_TYPE=$BUILD_TYPE \ 
          -DLLVM_TARGETS_TO_BUILD="X86;" \
          -DCMAKE_INSTALL_PREFIX:PATH=/llvm/out \
          -DLLVM_ENABLE_PEDANTIC=OFF \
          -DLLVM_ENABLE_PIC=ON \
          -DLLVM_REQUIRES_RTTI=ON \
          -DLLVM_INCLUDE_TESTS=OFF \
          -DLLVM_INCLUDE_GO_TESTS=OFF \
          -DLLVM_INCLUDE_EXAMPLES=OFF \
          -DLLVM_INCLUDE_DOCS=OFF \
          -DLLVM_BINDINGS_LIST=" " \
          -DCPACK_GENERATOR="TGZ" \
          /llvm/repo

RUN ninja package

WORKDIR /llvm
RUN mv /llvm/build/LLVM-* /llvm/ && rm -rf /llvm/build 

RUN echo '#!/bin/sh' > cpy.sh && \ 
    echo 'cp *.tar.gz /host/' >> cpy.sh && \
    chmod +x cpy.sh

# Define default command.
CMD ["./cpy.sh"]

