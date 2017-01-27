# Dockerfile for Seahorn

# OS image
FROM ubuntu:14.04

MAINTAINER Temesghen Kahsai <lememta@gmail.com>

ENV SEAHORN=/home/seahorn/seahorn_bin
ENV PATH="/home/seahorn/seahorn/bin:$PATH"


# Install
RUN \
  sudo apt-get update -qq && \
  sudo apt-get upgrade -qq && \
  sudo apt-get install bridge-utils && \
  apt-get install -qq build-essential clang-3.6 && \
  apt-get install -qq software-properties-common && \
  apt-get install -qq curl git ninja-build man subversion vim wget cmake && \
  apt-get install -qq libboost-program-options-dev && \
  apt-get install python2.7 python2.7-dev -y && \
  apt-get install -y libboost1.55-all-dev && \
  apt-get install --yes libgmp-dev && \
  apt-get install --yes python-pip

RUN \
  export LZ="$TRAVIS_BUILD_DIR/../lz" && \
  mkdir -p $LZ && \
  wget --output-document=llvm-z3.tar.gz https://www.dropbox.com/s/cipjz38k3boyd1v/llvm-3.6-z3.tar.gz?dl=1 && \
  tar xvf llvm-z3.tar.gz -C $LZ && \
  ls $LZ && \
  sudo pip install lit && \
  sudo pip install OutputCheck


RUN \
  git clone https://github.com/seahorn/seahorn && \
  cd seahorn && \
  ls && \
  mkdir -p build && \
  cd build && \
  mv $LZ/run run && \
  /usr/bin/cmake -DBOOST_ROOT=$BOOST_ROOT -DZ3_ROOT=run -DLLVM_DIR=$(pwd)/run/share/llvm/cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_PROGRAM_PATH=/usr/bin  -DCMAKE_INSTALL_PREFIX=run ../ && \
  /usr/bin/cmake --build . --target extra && \
  ls ../ && \
  /usr/bin/cmake --build . && \
  /usr/bin/cmake --build . && \
  /usr/bin/cmake --build . --target install && \
  ls run/bin/ && \
  run/bin/sea -h && \
  /usr/bin/cmake --build . --target test-simple

ENV C_INCLUDE_PATH="/home/seahorn/include/seahorn:$C_INCLUDE_PATH"
ENV PATH="/home/seahorn/build/run/bin:$PATH"
