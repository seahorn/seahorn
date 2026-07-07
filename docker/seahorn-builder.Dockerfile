# SeaHorn builder image that builds binary SeaHorn release package
# Primarily used by the CI
# Arguments:
#  - BUILDPACK_IMAGE: registry/owner of the buildpack-deps base image
#                     (published to GHCR by the buildpack-deps workflow)
#  - BASE-IMAGE: jammy-llvm16
#  - BUILD_TYPE: Debug, RelWithDebInfo, Coverage
ARG BUILDPACK_IMAGE=ghcr.io/seahorn/buildpack-deps-seahorn
ARG BASE_IMAGE=jammy-llvm16
FROM ${BUILDPACK_IMAGE}:${BASE_IMAGE}

# Assume that docker-build is ran in the top-level SeaHorn directory
COPY . /seahorn

ARG BUILD_TYPE=RelWithDebInfo

# The build commands live in docker/build_seahorn.sh, shared with the CI
# `docker run` build (which mounts a persistent ccache directory). Inside this
# image there is no cache mount, so ccache simply has no prior entries to reuse.
RUN BUILD_TYPE=${BUILD_TYPE} CCACHE_DIR=/seahorn/.ccache \
  bash /seahorn/docker/build_seahorn.sh

ENV PATH "/seahorn/build/run/bin:$PATH"
WORKDIR /seahorn
