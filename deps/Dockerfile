#
# Dockerfile for SeaHorn
# This produces package in /seahorn/build
# Arguments:
#  - UBUNTU:     trusty, xenial
#  - BUILD_TYPE: Debug, Release
#

ARG UBUNTU

# Pull base image.
FROM buildpack-deps:$UBUNTU

ARG BUILD_TYPE
RUN echo "Build type set to: $BUILD_TYPE"

# Install deps.
RUN \
  apt-get update && \
  apt-get install -yqq software-properties-common python-software-properties && \
  add-apt-repository --yes ppa:ubuntu-toolchain-r/test && \
  apt-get update && \
  apt-get upgrade -yqq && \
  apt-get install -yqq binutils-gold cmake cmake-data xdot g++-5 \
                       ninja-build libgraphviz-dev libstdc++5 \
                       libgmp-dev libmpfr-dev clang-3.8 libiomp-dev \
                       python-dev python-pip python-setuptools

RUN pip install lit OutputCheck
RUN easy_install networkx pygraphviz

# Use gold instead of bfd for much faster linking.
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.gold" 20 && \
    update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.bfd" 10


WORKDIR /tmp/dockerutils

# Create a helper script that works as switch (VAL) { Key0 : Val0, ...}.
# This is to work around docker limitations and pass right correct flag to the
# python configuration script.
RUN echo '#!/bin/sh' > switch.sh && \ 
    echo 'VAL=$1;shift;while test $# -gt 0;do if [ "$1" = "$VAL" ];then echo $2;exit 0;fi;shift;shift;done' >> switch.sh && \
    chmod +x switch.sh


RUN /tmp/dockerutils/switch.sh $BUILD_TYPE Debug "debug" Release "rel" \
    > /tmp/dockerutils/dt_out.txt
RUN export BT=$(cat /tmp/dockerutils/dt_out.txt) && \
    export UB=$(lsb_release --a 2>&1 | cut -f2 | tail -n 1) && \
    echo "$UB"_"$BT" > /tmp/dockerutils/prefix.txt && \
    cat /tmp/dockerutils/prefix.txt

RUN mkdir -p /deps
WORKDIR /deps
RUN export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export DEPS_LINK=$(echo https://github.com/kuhar/seahorn_deps/releases/download/v0.1/"$PREFIX".tar.gz) && \
    wget $DEPS_LINK

RUN export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export DEPS_TAR=$(echo "$PREFIX".tar.gz) && \
    tar -xvf $DEPS_TAR && \
    tar -xvf boost162.tar.gz && \
    tar -xvf z3.tar.gz && \
    tar -xvf llvm38.tar.gz && \
    rm *.tar.gz

RUN ls -al --block-size=M 1>&2

RUN mkdir -p /seahorn
WORKDIR /seahorn

# Checkout SeaHorn.
RUN git clone https://github.com/seahorn/seahorn ./ -b master --depth=10
RUN mkdir -p /seahorn/build
WORKDIR /seahorn/build

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
          ../

RUN cmake --build . --target extra  && cmake ..
RUN cmake --build . --target crab  && cmake ..
RUN cmake --build . --target install
RUN cmake --build . --target package

ENV PATH "/seahorn/build/run/bin:$PATH"

WORKDIR /seahorn

RUN echo '#!/bin/sh' > /tmp/cpy.sh && \ 
    echo 'cp /seahorn/build/*.tar.gz /host/ && bash' >> /tmp/cpy.sh && \
    chmod +x /tmp/cpy.sh

# Define default command.
CMD ["/tmp/cpy.sh"]
