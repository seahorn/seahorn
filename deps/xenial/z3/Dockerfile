#
# z3/spacer xenial Dockerfile for SeaHorn
# This produces z3_release.tar and z3_debug.tar in /z3.
#

# Pull base image.
FROM buildpack-deps:xenial

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

RUN mkdir -p /z3/release

# Build release configuration.
RUN python /z3/repo/scripts/mk_make.py --prefix=/z3/release
WORKDIR /z3/repo/build
RUN make -j$(nproc)
RUN make install -j$(nproc)

RUN tar -cvf /z3/z3_release.tar /z3/release

RUN rm -rf /z3/release
RUN rm -rf /z3/repo/build
RUN mkdir -p /z3/debug

# Build debug configuration.
WORKDIR /z3/repo
RUN python /z3/repo/scripts/mk_make.py --prefix=/z3/debug -d
WORKDIR /z3/repo/build
RUN make -j$(nproc)
RUN make install -j$(nproc)

RUN tar -cvf /z3/z3_debug.tar /z3/debug

RUN rm -rf /z3/debug
RUN rm -rf /z3/build/*
WORKDIR /z3

# Define default command.
CMD ["bash"]
