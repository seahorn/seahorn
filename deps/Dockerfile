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
    echo "$UB"_"$BT"_ > /tmp/dockerutils/prefix.txt && \
    cat /tmp/dockerutils/prefix.txt

RUN mkdir -p /deps
WORKDIR /deps
RUN export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export BOOST_LINK=$(echo https://github.com/kuhar/seahorn_deps/raw/master/"$PREFIX"boost162.tar) && \
    wget $BOOST_LINK

RUN export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export Z3_LINK=$(echo https://github.com/kuhar/seahorn_deps/raw/master/"$PREFIX"z3.tar) && \
    wget $Z3_LINK

RUN export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export LLVM_LINK=$(echo https://github.com/kuhar/seahorn_deps/raw/master/"$PREFIX"llvm38.tar.gz) && \
    wget $LLVM_LINK

RUN export PREFIX=$(cat /tmp/dockerutils/prefix.txt) && \
    export BOOST_TAR=$(echo "$PREFIX"boost162.tar) && \
    export Z3_TAR=$(echo "$PREFIX"z3.tar) && \
    export LLVM_TAR=$(echo "$PREFIX"llvm38.tar.gz) && \
    tar -xvf $BOOST_TAR && rm $BOOST_TAR && \
    tar -xvf $Z3_TAR && rm $Z3_TAR && \
    tar -xvf $LLVM_TAR && rm $LLVM_TAR

RUN ls -al --block-size=M 1>&2

RUN mkdir -p /seahorn
WORKDIR /seahorn

# Checkout SeaHorn.
RUN git clone https://github.com/seahorn/seahorn ./ --depth=10
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
# Define default command.
CMD ["bash"]
