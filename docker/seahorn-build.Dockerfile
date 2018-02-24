#
# Dockerfile for SeaHorn build image
# produces a container containing dependencies
# Arguments:
#  - UBUNTU:     trusty, xenial
#  - BUILD_TYPE: Debug, Release
#

ARG UBUNTU

# Pull base image.
FROM buildpack-deps:$UBUNTU

ARG BUILD_TYPE
RUN echo "Build type set to: $BUILD_TYPE" && \
     # Install deps.
    apt-get update && \
    apt-get install -yqq software-properties-common python-software-properties && \
    add-apt-repository --yes ppa:ubuntu-toolchain-r/test && \
    apt-get update && \
    apt-get upgrade -yqq && \
    apt-get install -yqq binutils-gold cmake cmake-data xdot g++-5 \
                       ninja-build libgraphviz-dev libstdc++5 \
                       libgmp-dev libmpfr-dev libiomp-dev \
                       python-dev python-pip python-setuptools && \
    pip install lit OutputCheck && \
    easy_install networkx pygraphviz && \
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
    export DEPS_LINK=$(echo https://github.com/seahorn/seahorn-ext-deps/releases/download/v0.1/"$PREFIX".tar.gz) && \
    curl -sSOL $DEPS_LINK && \
    export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export DEPS_TAR=$(echo "$PREFIX".tar.gz) && \
    tar -xf $DEPS_TAR && \
    tar -xf boost162.tar.gz && \
    tar -xf z3.tar.gz && \
    tar -xf llvm38.tar.gz && \
    rm *.tar.gz && \
#   ls -al --block-size=M 1>&2 && \
    mkdir -p /seahorn && \
    # download clang
    mkdir /clang-3.8 && \
    if [ "$UBUNTU" = "xenial" ] ; \
      then curl http://releases.llvm.org/3.8.0/clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-16.04.tar.xz ; \
      else curl http://releases.llvm.org/3.8.0/clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-14.04.tar.xz ; \
    fi \
    | tar -xJf - -C /clang-3.8 --strip-components=1
    
WORKDIR /seahorn
