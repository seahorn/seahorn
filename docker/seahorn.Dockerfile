#
# Minimal Dockerfile for SeaHorn
#
# Container with SeaHorn installed along with all build dependencies, but
# without any of the build by-products
#

FROM seahorn/buildpack-deps-seahorn:bionic-llvm10

ENV SEAHORN=/home/usea/seahorn/bin/sea PATH="$PATH:/home/usea/seahorn/bin"
USER root


# setup default user
RUN useradd -ms /bin/bash usea && \
  echo usea:horn | chpasswd && \
  usermod -aG sudo usea && \
  echo "PS1='\${debian_chroot:+(\$debian_chroot)}\[\033[01;32m\]\u@\h\[\033[00m\]:\[\033[01;34m\]\w\n\[\033[00m\]\\\$ '" >> /home/usea/.bashrc

USER usea
WORKDIR /home/usea

COPY SeaHorn-10.*.tar.gz /tmp
RUN mkdir -p /home/usea/seahorn && \
  tar xf /tmp/SeaHorn-10.*.tar.gz -C seahorn --strip-components=1 

# cleanup
USER root
RUN rm -rf /tmp/SeaHorn-10.*.tar.gz

# user and directory for when the container starts interactively
USER usea
WORKDIR /home/usea

