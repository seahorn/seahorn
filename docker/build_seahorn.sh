#!/usr/bin/env bash
#
# Build SeaHorn and produce the binary release tarball (SeaHorn-*.tar.gz).
#
# Single source of truth for the build commands, used in two ways:
#   * baked into an image by docker/seahorn-builder.Dockerfile
#     (COPY . /seahorn ; RUN bash docker/build_seahorn.sh), and
#   * invoked via `docker run` in CI with the source tree and a persistent
#     ccache directory mounted, so C/C++ compilation is incrementally cached
#     across builds (ccache caches object files; ninja still re-links).
#
# Environment:
#   SRC_DIR     SeaHorn source tree           (default: /seahorn)
#   BUILD_TYPE  CMake build type              (default: RelWithDebInfo)
#   CCACHE_DIR  ccache cache directory        (default: /ccache)
#
set -euo pipefail

SRC_DIR=${SRC_DIR:-/seahorn}
BUILD_TYPE=${BUILD_TYPE:-RelWithDebInfo}
# LLVM major version; the dev17 branch builds with clang/LLVM 17.
LLVM_VERSION=${LLVM_VERSION:-17}
export CCACHE_DIR=${CCACHE_DIR:-/ccache}
# Make cached files world-readable so the host runner (a different uid) can
# pack the cache directory with actions/cache after a containerized build.
export CCACHE_UMASK=${CCACHE_UMASK:-000}
export CCACHE_MAXSIZE=${CCACHE_MAXSIZE:-5G}
# The source path is stable (/seahorn) across runs, so absolute paths baked
# into the cache key stay consistent and hit rates remain high.

# The published base image (buildpack-deps-seahorn) may predate ccache being
# added to its Dockerfile; install it on demand (same pattern as filecheck).
if ! command -v ccache >/dev/null 2>&1; then
  apt-get update -qq && apt-get install -yqq ccache
fi
# Regression tooling may be missing from a stale base image.
pip3 install --quiet filecheck || true

# When the source tree is bind-mounted in CI it is owned by the host runner
# user, but this script runs as root in the container; tell git not to reject
# the differing owner (otherwise the `extra` clone/version steps fail).
git config --global --add safe.directory '*' || true

cd "$SRC_DIR"
# ccache provides incrementality, not the build directory: always start from a
# clean tree and drop any third-party clones left by a previous run.
rm -rf build debug release clam sea-dsa llvm-seahorn
mkdir build
cd build

ccache --zero-stats >/dev/null 2>&1 || true

cmake .. -GNinja \
  -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" \
  -DZ3_ROOT=/opt/z3-4.8.9 \
  -DYICES2_HOME=/opt/yices-2.6.1 \
  -DCMAKE_INSTALL_PREFIX=run \
  -DCMAKE_CXX_COMPILER=clang++-${LLVM_VERSION} \
  -DCMAKE_C_COMPILER=clang-${LLVM_VERSION} \
  -DCMAKE_C_COMPILER_LAUNCHER=ccache \
  -DCMAKE_CXX_COMPILER_LAUNCHER=ccache \
  -DSEA_ENABLE_LLD=ON \
  -DCPACK_GENERATOR="TGZ" \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DWITH_CLAM=OFF

# `extra` clones the third-party projects; re-run cmake to pick them up.
cmake --build . --target extra
cmake ..
cmake --build . --target install
cmake --build . --target units_z3
cmake --build . --target units_yices2
cmake --build . --target test_type_checker
cmake --build . --target test_hex_dump
cmake --build . --target package

units/units_z3
units/units_yices2
units/units_type_checker

echo "==== ccache statistics ===="
ccache --show-stats || true
