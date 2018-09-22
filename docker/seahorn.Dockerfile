#
# Minimal Dockerfile for SeaHorn
# produces a lightweight container with SeaHorn
# Arguments:
#  - BASE_IMAGE: seahorn/seahorn (for use on Travis only), buildpack-deps (default)
#

ARG BASE_IMAGE=ubuntu:16.04
FROM $BASE_IMAGE

ARG BASE_IMAGE=ubuntu:16.04
ENV SEAHORN=/opt/seahorn/bin/sea PATH="$PATH:/opt/seahorn/bin:/opt/llvm/bin"
USER root

RUN if [ "$BASE_IMAGE" != "seahorn/seahorn" ] && [ "$BASE_IMAGE" != "ubuntu:16.04" ] ; \
      then exit -1 ; \
      else echo "pulling from $BASE_IMAGE" ; \
    fi && \
    rm -rf /opt && \
    mkdir -p /opt
COPY *.tar.gz /opt
WORKDIR /opt

# extract seahorn
RUN mkdir -p seahorn && \
    tar -xf *.tar.gz -C seahorn --strip-components=1 && \
    rm -f *.tar.gz && \
    if [ "$BASE_IMAGE" != "seahorn/seahorn" ] ; \
      then \
        # install test dependencies & tools
        apt-get update && \
        apt-get install --no-install-recommends -yqq \
            sudo curl build-essential vim-tiny gdb \
            python-dev python-setuptools python-pip libgraphviz-dev libc6-dev-i386 && \
        pip install lit OutputCheck && \
        easy_install networkx pygraphviz && \
        # get supported llvm version
        mkdir /opt/llvm && \
        curl -sL https://github.com/seahorn/seahorn-ext-deps/releases/download/v0.1/xenial_rel_llvm38.tar.gz \
        | tar -xzf - -C /opt/llvm --strip-components=1 && \
        # download clang
        mkdir /clang-3.8 && \
        if [ "$UBUNTU" = "xenial" ] ; \
          then curl -s http://releases.llvm.org/3.8.0/clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-16.04.tar.xz ; \
          else curl -s http://releases.llvm.org/3.8.0/clang+llvm-3.8.0-x86_64-linux-gnu-ubuntu-14.04.tar.xz ; \
        fi \
        | tar -xJf - -C /clang-3.8 --strip-components=1 && \
        apt-get remove -yqq curl && \
        rm -rf /var/lib/apt/lists/* && \
        # set up default user
        useradd -ms /bin/bash usea && \
        echo usea:horn | chpasswd && \
        usermod -aG sudo usea ; \
    fi && \
    # symlink clang
    cd seahorn/bin && \
    ln -s /clang-3.8/bin/clang clang && \
    ln -s /clang-3.8/bin/clang++ clang++ && \
    # finish setting up permissions
    chmod -R 777 /opt/seahorn

WORKDIR seahorn
USER usea
