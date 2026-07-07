#
# SeaHorn build image. Contains all the necessary dependencies
# to build SeaHorn and related tools. Does not contain the tools
# themselves. Used by the CI to start the build
#

ARG BASE_IMAGE=jammy-scm
# Base image with usual build dependencies
FROM buildpack-deps:$BASE_IMAGE

# LLVM major version to install. Jammy's own archive stops at clang-15, so the
# toolchain comes from apt.llvm.org (which also serves 15, so this works for
# rebuilding the llvm15 image too).
ARG LLVM_VERSION=16

# Install dependencies
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
  apt-get install -yqq software-properties-common wget gnupg && \
  wget -qO- https://apt.llvm.org/llvm-snapshot.gpg.key | apt-key add - && \
  add-apt-repository -y "deb http://apt.llvm.org/jammy/ llvm-toolchain-jammy-${LLVM_VERSION} main" && \
  apt-get update && \
  apt-get upgrade -yqq && \
  apt-get install -yqq cmake cmake-data unzip \
      zlib1g-dev libzstd-dev \
      ninja-build libgraphviz-dev \
      ccache \
      libgmp-dev libmpfr-dev \
      libboost1.74-dev \
      python3-pip \
      less vim \
      gcc-multilib \
      sudo \
      graphviz libgraphviz-dev python3-pygraphviz \
      lcov gcovr rsync \
      clang-${LLVM_VERSION} lldb-${LLVM_VERSION} lld-${LLVM_VERSION} \
      clang-format-${LLVM_VERSION} llvm-${LLVM_VERSION}-dev && \
  pip3 install lit filecheck && \
  pip3 install networkx && \
  mkdir seahorn

# Install z3 v4.8.9 since bionic comes with much older version
WORKDIR /tmp
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.9/z3-4.8.9-x64-ubuntu-16.04.zip && \
  unzip z3-4.8.9-x64-ubuntu-16.04.zip && \
  mv z3-4.8.9-x64-ubuntu-16.04 /opt/z3-4.8.9

# Install yices 2.6.1
RUN curl -sSOL https://yices.csl.sri.com/releases/2.6.1/yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz && \
  tar xf yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz && \
  cd /tmp/yices-2.6.1/ && \
  ./install-yices /opt/yices-2.6.1

WORKDIR /seahorn
