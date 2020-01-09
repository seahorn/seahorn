#
# Minimal Dockerfile for SeaHorn and verifyTrusty environment
# produces a lightweight container with SeaHorn, trusty source code and compiled harness files
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
        apt-get --yes --force-yes install software-properties-common && \
        add-apt-repository ppa:deadsnakes/ppa && \
        apt-get update && \
        apt-get install --no-install-recommends -yqq \
            sudo curl build-essential vim-tiny gdb \
            python-dev python-setuptools python-pip libgraphviz-dev libc6-dev-i386 \
            git python3 python3-pip bear libssl-dev zip && \
        pip install --upgrade pip && \
        python -m pip install setuptools --upgrade && \
        python -m pip install lit OutputCheck && \
        python -m pip install networkx==2.2 pygraphviz && \
        python3 -m pip install setuptools --upgrade && \
        python3 -m pip install pyyaml && \
        # get supported llvm version
        mkdir /opt/llvm && \
        curl -sL https://github.com/seahorn/seahorn-ext-deps/releases/download/5.0-deep-dev/xenial_rel_llvm50.tar.gz \
        | tar -xzf - -C /opt/llvm --strip-components=1 && \
        # download clang
        mkdir /clang-5.0 && \
        curl -s http://releases.llvm.org/5.0.0/clang+llvm-5.0.0-linux-x86_64-ubuntu16.04.tar.xz \
        | tar -xJf - -C /clang-5.0 --strip-components=1 && \
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

WORKDIR /opt

RUN echo "pulling verify trusty environment" && \
    # installing repo
    mkdir ~/bin && PATH=~/bin:$PATH && \
    curl https://storage.googleapis.com/git-repo-downloads/repo > ~/bin/repo && \
    chmod a+x ~/bin/repo && \
    git clone https://github.com/danblitzhou/verifyTrusty.git && \
    cd verifyTrusty && \
    repo init -u https://android.googlesource.com/trusty/manifest -b master && \
    repo sync -j32 && \
    git remote update && git pull origin master && cp bear_build.py trusty/vendor/google/aosp/scripts/build.py && \
    trusty/vendor/google/aosp/scripts/build.py generic-arm32 && \
    python3 seahorn/gen_bc.py --jobs storage_ipc_indirect_handlers storage_ipc_msg_buffer storage_ipc_port_create_destroy
USER usea
