#
# boost Dockerfile for SeaHorn
# This produces packages in /boost.
# Arguments:
#  - UBUNTU:     trusty, xenial
#  - BUILD_TYPE: Debug, Release
#

ARG UBUNTU

# Pull base image.
FROM buildpack-deps:$UBUNTU

ARG BUILD_TYPE
RUN echo Build type set to: $BUILD_TYPE

WORKDIR /tmp/dockerutils

# Create a helper script that works as switch (VAL) { Key0 : Val0, ...}.
# This is to work around docker limitations and pass right correct flag to the
# python configuration script.

RUN echo '#!/bin/sh' > switch.sh && \ 
    echo 'VAL=$1;shift;while test $# -gt 0;do if [ "$1" = "$VAL" ];then echo $2;exit 0;fi;shift;shift;done' >> switch.sh && \
    chmod +x switch.sh

# If BUILD_TYPE is Debug the additional CXX flags. 
# Save them to a temporary file, as every run command runs in its own shell.
# Assume AVX support.
RUN /tmp/dockerutils/switch.sh $BUILD_TYPE Debug "debug" Release "release" \
    > /tmp/dockerutils/out.txt

# Install deps
RUN \
  apt-get update && \
  apt-get install -yqq binutils-gold libicu-dev libbz2-dev python-dev autotools-dev

# Use gold instead of bfd for much faster linking.
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.gold" 20
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.bfd" 10

WORKDIR /boost
RUN mkdir -p /boost/repo

# Checkout boost.
RUN git clone https://github.com/boostorg/boost.git -b boost-1.62.0 \
              --depth=1 --recursive ./repo

RUN mkdir -p /boost/out ; mkdir -p /boost/build

# Build selected configuration. Use the file with a saved flag to pick
# release or debug configuration.

WORKDIR /boost/repo

RUN ./bootstrap.sh

# Generate headers.
RUN ./b2 -j$(nproc) \
    --build-type=complete \
    --layout=versioned \
    --prefix=/boost/out headers 

# Generate shared libraries.
RUN ./b2 -j$(nproc) \
         --layout=versioned \
         --prefix=/boost/out \
         --build-dir=/boost/build \
         --build-type=complete \
         --without-mpi \
         variant=$(cat /tmp/dockerutils/out.txt) \
         link=shared \
         install

RUN cd /boost && \
    tar -cvf /boost/boost162.tar ./out

RUN rm -rf /boost/out ; rm -rf /z3/boost/build ; rm -rf /tmp/dockerutils

WORKDIR /boost

# Define default command.
CMD ["bash"]
