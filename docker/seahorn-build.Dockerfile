#
# Dockerfile for SeaHorn build image
# produces a container containing dependencies
# Arguments:
#  - UBUNTU:     trusty, xenial, bionic
#  - BUILD_TYPE: Debug, Release
#

ARG UBUNTU

# Pull base image.
FROM buildpack-deps:$UBUNTU

ARG BUILD_TYPE
RUN echo "Build type set to: $BUILD_TYPE" && \
     # Install deps.
    apt-get update && \
    apt-get install -yqq software-properties-common && \
    if [ "$UBUNTU" = "trusty" ] ; \
      then apt-get install -yqq python-software-properties ; \
    fi && \
    add-apt-repository --yes ppa:ubuntu-toolchain-r/test && \
    apt-get update && \
    apt-get upgrade -yqq && \
    apt-get install -yqq binutils-gold cmake cmake-data xdot g++-5 \
                       ninja-build libgraphviz-dev libstdc++5 \
                       libgmp-dev libmpfr-dev libiomp-dev \
                       python-dev python-pip python-setuptools \
                       lcov ggcov && \
    pip install lit OutputCheck && \
    pip install networkx==2.2 pygraphviz && \
    # Use gold instead of bfd for much faster linking.
    update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.gold" 20 && \
    update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.bfd" 10


WORKDIR /tmp/dockerutils

# Create a helper script that works as switch (VAL) { Key0 : Val0, ...}.
# This is to work around docker limitations and pass right correct flag to the
# python configuration script.
RUN echo '#!/bin/sh' > switch.sh && \ 
    echo 'VAL=$1;shift;while test $# -gt 0;do if [ "$1" = "$VAL" ];then echo $2;exit 0;fi;shift;shift;done' >> switch.sh && \
    chmod +x switch.sh && \
    /tmp/dockerutils/switch.sh $BUILD_TYPE Debug "debug" Release "rel" \
    > /tmp/dockerutils/dt_out.txt && \
    export BT=$(cat /tmp/dockerutils/dt_out.txt) && \
    export UB=$(lsb_release --a 2>&1 | cut -f2 | tail -n 1) && \
    echo "$UB"_"$BT" > /tmp/dockerutils/prefix.txt && \
    cat /tmp/dockerutils/prefix.txt && \
    mkdir -p /deps

WORKDIR /deps
RUN export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export DEPS_BASE=$(echo https://github.com/seahorn/seahorn-ext-deps/releases/download/5.0-deep-dev/"$PREFIX") && \
    curl -sSOL "$DEPS_BASE"_boost_1_68.tar.gz && \
    tar -xf "$PREFIX"_boost_1_68.tar.gz && \
    curl -sSOL "$DEPS_BASE"_z3.tar.gz && \
    tar -xf "$PREFIX"_z3.tar.gz && \
    curl -sSOL "$DEPS_BASE"_yices-2.6.1.tar.gz && \
    tar -xf "$PREFIX"_yices-2.6.1.tar.gz && \
    curl -sSOL "$DEPS_BASE"_llvm50.tar.gz && \
    tar -xf "$PREFIX"_llvm50.tar.gz && \
#   ls -al --block-size=M 1>&2 && \
    mkdir -p /seahorn && \
    # download clang
    mkdir /clang-5.0 && \
    if [ "$UBUNTU" = "trusty" ] ; \
      then curl -s http://releases.llvm.org/5.0.0/clang+llvm-5.0.0-linux-x86_64-ubuntu14.04.tar.xz ; \
      else curl -s http://releases.llvm.org/5.0.0/clang+llvm-5.0.0-linux-x86_64-ubuntu16.04.tar.xz ; \
    fi \
    | tar -xJf - -C /clang-5.0 --strip-components=1
    
WORKDIR /seahorn
