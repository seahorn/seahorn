#
# SeaHorn build image. Contains all the necessary dependencies
# to build SeaHorn and related tools. Does not contain the tools
# themselves. Used by the CI to start the build
#

ARG BASE_IMAGE=jammy-scm
# Base image with usual build dependencies
FROM buildpack-deps:$BASE_IMAGE

# Install dependencies
ARG DEBIAN_FRONTEND=noninteractive
RUN apt-get update && \
  apt-get install -yqq software-properties-common && \
  apt-get update && \
  apt-get upgrade -yqq && \
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
      lcov gcovr rsync \
      clang-12 lldb-12 lld-12 clang-format-12 && \
  pip3 install lit OutputCheck && \
  pip3 install networkx && \
  mkdir seahorn

# Install z3 v4.8.9 since bionic comes with much older version
# Install yices 2.6.1 (still not sure why)
WORKDIR /tmp
RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.9/z3-4.8.9-x64-ubuntu-16.04.zip && \
  unzip z3-4.8.9-x64-ubuntu-16.04.zip && \
  mv z3-4.8.9-x64-ubuntu-16.04 /opt/z3-4.8.9 && \
  curl -sSOL https://yices.csl.sri.com/releases/2.6.1/yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz && \
  tar xf yices-2.6.1-x86_64-pc-linux-gnu-static-gmp.tar.gz && \
  mv /tmp/yices-2.6.1/ /opt

WORKDIR /seahorn
