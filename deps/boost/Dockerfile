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

# If BUILD_TYPE is Debug we need to add 'debug' the additional CXX flags. 
# Save them to a temporary file, as every run command runs in its own shell.
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

RUN wget --output-document=boost.tar.bz2 https://downloads.sourceforge.net/project/boost/boost/1.68.0/boost_1_68_0.tar.bz2

RUN tar -xvf boost.tar.bz2 && mv -T /boost/boost_1_68_0 /boost/repo && rm boost.tar.bz2

RUN mkdir -p /boost/out

# Build selected configuration. Use the file with a saved flag to pick
# release or debug configuration.

WORKDIR /boost/repo

RUN ./bootstrap.sh --with-libraries=date_time,filesystem,system,iostreams,regex,test

# Generate libs and headers.
RUN ./b2 -j$(nproc) threading=multi -d0

RUN mkdir -p /boost/out ; mkdir -p /boost/out/boost ; mkdir -p /boost/out/boost/include
RUN cp -r /boost/repo/boost /boost/out/boost/include/boost
RUN cp -r /boost/repo/stage/lib /boost/out/boost/lib

RUN ls 1>&2 /boost/out

RUN cd /boost/out && tar -czvf /boost/boost_1_68.tar.gz ./

RUN rm -rf /boost/out ; rm -rf /boost/repo ; rm -rf /tmp/dockerutils

WORKDIR /boost

RUN echo '#!/bin/sh' > cpy.sh && \ 
    echo 'cp *.tar.gz /host/' >> cpy.sh && \
    chmod +x cpy.sh

# Define default command.
CMD ["./cpy.sh"]
