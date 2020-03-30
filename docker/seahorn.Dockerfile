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

RUN if [ "$BASE_IMAGE" != "seahorn/seahorn-llvm5" ] && [ "$BASE_IMAGE" != "ubuntu:16.04" ] ; \
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
    if [ "$BASE_IMAGE" != "seahorn/seahorn-llvm5" ] ; \
      then \
        # install test dependencies & tools
        apt-get update && \
        apt-get install --no-install-recommends -yqq \
            sudo curl build-essential vim-tiny gdb \
            python-dev python-setuptools python-pip libgraphviz-dev libc6-dev-i386 && \
        pip install --upgrade pip && \
        python -m pip install setuptools --upgrade && \
        python -m pip install lit OutputCheck && \
        python -m pip install networkx==2.2 pygraphviz && \
        # get supported llvm version
        mkdir /opt/llvm && \
        curl -sL https://github.com/seahorn/seahorn-ext-deps/releases/download/5.0-deep-dev/xenial_rel_llvm50.tar.gz \
        | tar -xzf - -C /opt/llvm --strip-components=1 && \
        # download clang
        mkdir /clang-5.0 && \
        curl -s https://releases.llvm.org/5.0.0/clang+llvm-5.0.0-linux-x86_64-ubuntu16.04.tar.xz \
        | tar -xJf - -C /clang-5.0 --strip-components=1 && \
        apt-get remove -yqq curl && \
        rm -rf /var/lib/apt/lists/* && \
        # set up default user
        useradd -ms /bin/bash usea && \
        echo usea:horn | chpasswd && \
        usermod -aG sudo usea ; \
    fi && \
    # symlink clang
    cd seahorn/bin && \
    ln -s /clang-5.0/bin/clang clang && \
    ln -s /clang-5.0/bin/clang++ clang++ && \
    # finish setting up permissions
    chmod -R 777 /opt/seahorn && \
    # make the environment more pleasant to use
    ln -sfn /usr/bin/vim.tiny /usr/bin/vim && \
    echo "PS1='\${debian_chroot:+(\$debian_chroot)}\[\033[01;32m\]\u@\h\[\033[00m\]:\[\033[01;34m\]\w\n\[\033[00m\]\\\$ '" >> /home/usea/.bashrc

WORKDIR seahorn
USER usea
