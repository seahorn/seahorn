#
# z3/spacer Dockerfile for SeaHorn
# This produces packages in /z3.
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

# If BUILD_TYPE is Debug the additional flag is "-d". Save it to a temporary file,
# as every run command runs in its own shell.
RUN /tmp/dockerutils/switch.sh $BUILD_TYPE Debug "-d" Release "" > /tmp/dockerutils/out.txt

# Install deps
RUN \
  apt-get update && \
  apt-get install -yqq binutils-gold

# Use gold instead of bfd for much faster linking.
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.gold" 20
RUN update-alternatives --install "/usr/bin/ld" "ld" "/usr/bin/ld.bfd" 10

WORKDIR /z3
RUN mkdir -p /z3/repo
WORKDIR /z3/repo

# Checkout z3/spacer3.
RUN git clone https://bitbucket.org/spacer/code.git ./ -b spacer3 --depth=1

RUN mkdir -p /z3/out ; mkdir -p /z3/out/z3

# Build selected configuration. Use the file with a saved flag to pick
# release or debug configuration.

RUN export IS_DEBUG=$(cat /tmp/dockerutils/out.txt) && \
    python /z3/repo/scripts/mk_make.py --prefix=/z3/out/z3 --staticlib $IS_DEBUG
WORKDIR /z3/repo/build
RUN make -j$(nproc)
RUN make install -j$(nproc)

RUN cd /z3/out ; tar -czvf /z3/z3.tar.gz ./z3

RUN rm -rf /z3/out ; rm -rf /z3/repo/build ; rm -rf /tmp/dockerutils

WORKDIR /z3

RUN echo '#!/bin/sh' > cpy.sh && \ 
    echo 'cp *.tar.gz /host/' >> cpy.sh && \
    chmod +x cpy.sh

# Define default command.
CMD ["./cpy.sh"]

