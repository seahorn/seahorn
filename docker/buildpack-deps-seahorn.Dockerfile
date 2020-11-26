#
# SeaHorn build image. Contains all the necessary dependencies
# to build SeaHorn and related tools. Does not contain the tools
# themselves. Used by the CI to start the build
#

ARG BASE_IMAGE=bionic-scm
# Base image with usual build dependencies
FROM buildpack-deps:$BASE_IMAGE

# Install dependencies
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
  apt-get install -yqq software-properties-common && \
  add-apt-repository -y ppa:mhier/libboost-latest && \  
  apt-get update && \
  apt-get upgrade -yqq && \
  apt-get remove -yqq libboost1.65-dev && \
  apt-get install -yqq cmake cmake-data unzip \
      zlib1g-dev \
      ninja-build libgraphviz-dev \
      libgmp-dev libmpfr-dev \
      libboost1.74-dev \
      python3-pip \
      less vim \
      gcc-multilib \
      sudo \
      graphviz libgraphviz-dev python3-pygraphviz \
      lcov ggcov rsync && \
  pip3 install lit OutputCheck && \
  pip3 install networkx && \
  mkdir seahorn

# Install llvm10 from llvm repo since bionic comes with much older version
# Install z3 v4.8.9 since bionic comes with much older version
# Install yices 2.6.1 (not sure why)
WORKDIR /tmp
RUN wget https://apt.llvm.org/llvm.sh && \
  chmod +x llvm.sh && \
  ./llvm.sh 10 && \
  apt-get install -y clang-format-10 && \
  wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.9/z3-4.8.9-x64-ubuntu-16.04.zip && \
  unzip z3-4.8.9-x64-ubuntu-16.04.zip && \
  mv z3-4.8.9-x64-ubuntu-16.04 /opt/z3-4.8.9 && \
  curl -sSOL https://github.com/seahorn/seahorn-ext-deps/releases/download/5.0-deep-dev/bionic_rel_yices-2.6.1.tar.gz && \
  tar xf bionic_rel_yices-2.6.1.tar.gz && \
  mv /tmp/yices-2.6.1/ /opt

WORKDIR /seahorn
