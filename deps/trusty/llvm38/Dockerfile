#
# llvm-3.8 trusty Dockerfile for SeaHorn
# This produces llvm38_release.tar and llvm38_debug.tar in /llvm.
#

# Pull base image.
FROM buildpack-deps:trusty

# Install deps
RUN \
  apt-get update && \
  apt-get install -yqq binutils-gold cmake ninja-build libiomp-dev

# Use gold instead of bfd for much faster linking.
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.gold" 20
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.bfd" 10

WORKDIR /llvm

RUN mkdir -p /llvm/repo
WORKDIR /llvm/repo

# Checkout LLVM and Clang.
RUN git clone https://github.com/llvm-mirror/llvm/ ./ -b release_38 --depth=1
WORKDIR /llvm/repo/tools

RUN git clone https://github.com/llvm-mirror/clang -b release_38 --depth=1
RUN mkdir -p /llvm/build
RUN mkdir -p /llvm/release
WORKDIR /llvm/build

# Build release configuration.
RUN cmake -GNinja -DCMAKE_BUILD_TYPE=Release -DLLVM_TARGETS_TO_BUILD="X86;" \
          -DCMAKE_INSTALL_PREFIX:PATH=/llvm/release ../repo
RUN ninja install

WORKDIR /llvm
RUN tar -cvf /llvm/llvm38_release.tar /llvm/release

RUN rm -rf /llvm/release
RUN mkdir -p /llvm/debug
WORKDIR /llvm/build

# Build debug configuration.
RUN cmake -GNinja -DCMAKE_BUILD_TYPE=Debug -DLLVM_TARGETS_TO_BUILD="X86;" \
          -DCMAKE_INSTALL_PREFIX:PATH=/llvm/debug ../repo
RUN ninja install

WORKDIR /llvm
RUN rm -rf /llvm/build
RUN tar -cvf /llvm/llvm38_debug.tar /llvm/debug
RUN rm -rf /llvm/debug

# Define default command.
CMD ["bash"]
