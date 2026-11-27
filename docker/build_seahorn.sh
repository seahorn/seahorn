#!/usr/bin/env bash
# SPDX-FileCopyrightText: 2026 The SeaHorn Authors
# SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

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
#   BITWUZLA_VERSION  if set (e.g. 0.9.1), also build Bitwuzla, build SeaHorn
#               with it (--horn-bmc-solver=smt-bw), and run units_bitwuzla
#               (default: unset, no Bitwuzla)
#   BITWUZLA_PREFIX   where Bitwuzla and the GMP and MPFR it needs are
#               installed; kept if a previous run completed it, so CI can
#               cache it        (default: /opt/bitwuzla-$BITWUZLA_VERSION)
#   Z3_ROOT     Z3 distribution               (default: /opt/z3-4.8.9)
#   Z3_VERSION  if set (e.g. 5.1.0), build that Z3 from source into Z3_ROOT,
#               unless a previous run completed it there (CI caches it).
#               Z3 >= 4.15.8 uses C++20's <format>, which needs libstdc++
#               13: it is installed (ubuntu-toolchain-r/test), and clang
#               then builds SeaHorn with it too.
#   UNITS       unit tests to run, units/units_<name>
#               (default: "z3 yices2 type_checker"; add bitwuzla when
#               BITWUZLA_VERSION is set. units_z3 compares Z3's simplifier
#               output, which changes between Z3 versions.)
#
set -euo pipefail

SRC_DIR=${SRC_DIR:-/seahorn}
BUILD_TYPE=${BUILD_TYPE:-RelWithDebInfo}
# LLVM major version; the dev18 branch builds with clang/LLVM 18.
LLVM_VERSION=${LLVM_VERSION:-18}
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

# Bitwuzla 0.9.1 needs GMP >= 6.3 and MPFR >= 4.2.1 (its src/meson.build),
# newer than Ubuntu 22.04's, so they are built into the same prefix. Every
# download is pinned: tarballs by SHA-256, Bitwuzla by commit. Bitwuzla's
# libraries find GMP and MPFR next to them (rpath $ORIGIN), not the system's.
BITWUZLA_VERSION=${BITWUZLA_VERSION:-}
BITWUZLA_PREFIX=${BITWUZLA_PREFIX:-/opt/bitwuzla-${BITWUZLA_VERSION}}
build_bitwuzla() {
  local prefix=$1 commit src
  if [ -f "$prefix/.complete-$BITWUZLA_VERSION" ]; then
    echo "==== Bitwuzla $BITWUZLA_VERSION: reusing $prefix ===="
    return
  fi
  case "$BITWUZLA_VERSION" in
    0.9.1) commit=8d1eb01093ae54d9b4586456b69c3bf31000a4c2 ;;
    *) echo "build_seahorn.sh: no pinned commit for Bitwuzla $BITWUZLA_VERSION" >&2
       exit 1 ;;
  esac
  echo "==== Bitwuzla $BITWUZLA_VERSION: building into $prefix ===="
  # the prefix may be a mounted (cache) directory: empty it, keep it
  mkdir -p "$prefix"
  find "$prefix" -mindepth 1 -delete
  # tools a stale or minimal base image may lack (GMP's configure needs m4)
  local need=()
  command -v m4 >/dev/null 2>&1 || need+=(m4)
  command -v xz >/dev/null 2>&1 || need+=(xz-utils)
  command -v pkg-config >/dev/null 2>&1 || need+=(pkg-config)
  if [ ${#need[@]} -gt 0 ]; then
    apt-get update -qq && apt-get install -yqq "${need[@]}"
  fi
  src=$(mktemp -d)
  curl -sSfL https://ftp.gnu.org/gnu/gmp/gmp-6.3.0.tar.xz -o "$src/gmp.tar.xz"
  curl -sSfL https://ftp.gnu.org/gnu/mpfr/mpfr-4.2.1.tar.xz -o "$src/mpfr.tar.xz"
  sha256sum -c - <<EOF
a3c2b80201b89e68616f4ad30bc66aee4927c3ce50e33929ca819d5c43538898  $src/gmp.tar.xz
277807353a6726978996945af13e52829e3abd7a9a5b7fb2793894e18f1fcbb2  $src/mpfr.tar.xz
EOF
  tar -C "$src" -xf "$src/gmp.tar.xz"
  tar -C "$src" -xf "$src/mpfr.tar.xz"
  (cd "$src/gmp-6.3.0" && ./configure --quiet --prefix="$prefix" &&
     make -s -j"$(nproc)" && make -s install)
  (cd "$src/mpfr-4.2.1" && ./configure --quiet --prefix="$prefix" \
     --with-gmp="$prefix" && make -s -j"$(nproc)" && make -s install)
  printf '%s\n' 'meson==1.4.1 \' \
    '  --hash=sha256:d5acc3abae2dad3c70ddcbd10acac92b78b144d34d43f40f5b8ac31dfd8a826a \' \
    '  --hash=sha256:1b8aad738a5f6ae64294cc8eaba9a82988c1c420204484ac02ef782e5bba5f49' \
    > "$src/meson.txt"
  pip3 install --quiet --require-hashes -r "$src/meson.txt"
  git clone --quiet --depth 1 --branch "$BITWUZLA_VERSION" \
    https://github.com/bitwuzla/bitwuzla.git "$src/bitwuzla"
  if [ "$(git -C "$src/bitwuzla" rev-parse HEAD)" != "$commit" ]; then
    echo "build_seahorn.sh: Bitwuzla $BITWUZLA_VERSION is not commit $commit" >&2
    exit 1
  fi
  # libdir=lib: next to GMP and MPFR (Meson would pick lib/<multiarch>)
  (cd "$src/bitwuzla" &&
     PKG_CONFIG_PATH="$prefix/lib/pkgconfig" \
     CC=clang-${LLVM_VERSION} CXX=clang++-${LLVM_VERSION} \
     LDFLAGS='-Wl,-rpath,$ORIGIN' \
     ./configure.py release --shared --prefix "$prefix" &&
     meson configure build -Dlibdir=lib &&
     ninja -C build install)
  rm -rf "$src"
  touch "$prefix/.complete-$BITWUZLA_VERSION"
}
# Z3 from source (Z3_VERSION): the image's 4.8.9 is too old for the Bitwuzla
# tests' cross-checks, and newer Linux releases need a newer glibc than this
# image's. Pinned by commit; a static libz3, like the image's.
Z3_VERSION=${Z3_VERSION:-}
build_z3() {
  local prefix=$1 commit src
  if [ -f "$prefix/.complete-$Z3_VERSION" ]; then
    echo "==== Z3 $Z3_VERSION: reusing $prefix ===="
    return
  fi
  case "$Z3_VERSION" in
    5.1.0) commit=0b6cdcdbc65da25ef0f73ac9da210574d0f66cf8 ;;
    *) echo "build_seahorn.sh: no pinned commit for Z3 $Z3_VERSION" >&2
       exit 1 ;;
  esac
  echo "==== Z3 $Z3_VERSION: building into $prefix ===="
  mkdir -p "$prefix"
  find "$prefix" -mindepth 1 -delete
  src=$(mktemp -d)
  git clone --quiet --depth 1 --branch "z3-$Z3_VERSION" \
    https://github.com/Z3Prover/z3.git "$src/z3"
  if [ "$(git -C "$src/z3" rev-parse HEAD)" != "$commit" ]; then
    echo "build_seahorn.sh: Z3 $Z3_VERSION is not commit $commit" >&2
    exit 1
  fi
  cmake -S "$src/z3" -B "$src/z3/build" -GNinja \
    -DCMAKE_BUILD_TYPE=Release \
    -DCMAKE_INSTALL_PREFIX="$prefix" -DCMAKE_INSTALL_LIBDIR=lib \
    -DCMAKE_C_COMPILER=clang-${LLVM_VERSION} \
    -DCMAKE_CXX_COMPILER=clang++-${LLVM_VERSION} \
    -DZ3_BUILD_LIBZ3_SHARED=OFF -DZ3_BUILD_PYTHON_BINDINGS=OFF \
    -DZ3_BUILD_TEST_EXECUTABLES=OFF -DCMAKE_POSITION_INDEPENDENT_CODE=ON
  ninja -C "$src/z3/build" install
  rm -rf "$src"
  touch "$prefix/.complete-$Z3_VERSION"
}
if [ -n "$Z3_VERSION" ]; then
  if [ ! -d /usr/include/c++/13 ]; then
    apt-get update -qq
    apt-get install -yqq software-properties-common
    add-apt-repository -y ppa:ubuntu-toolchain-r/test
    apt-get update -qq
    apt-get install -yqq libstdc++-13-dev
  fi
  # the PPA's packages are not pinned: record what this run got
  dpkg-query -W -f='${Package} ${Version}\n' libstdc++6 libstdc++-13-dev
  # the GCC installation clang uses: its libstdc++ must have <format>
  clang++-${LLVM_VERSION} -v -E -x c++ /dev/null 2>&1 | grep 'Selected GCC installation'
  build_z3 "${Z3_ROOT:?Z3_VERSION needs Z3_ROOT}"
fi

BITWUZLA_CMAKE=()
if [ -n "$BITWUZLA_VERSION" ]; then
  build_bitwuzla "$BITWUZLA_PREFIX"
  # BITWUZLA_HOME makes Bitwuzla required: configuring fails without it
  BITWUZLA_CMAKE=(-DBITWUZLA_HOME="$BITWUZLA_PREFIX")
fi

cd "$SRC_DIR"
# ccache provides incrementality, not the build directory: always start from a
# clean tree and drop any third-party clones left by a previous run.
rm -rf build debug release clam sea-dsa llvm-seahorn
mkdir build
cd build

ccache --zero-stats >/dev/null 2>&1 || true

cmake .. -GNinja \
  -DCMAKE_BUILD_TYPE="${BUILD_TYPE}" \
  -DZ3_ROOT="${Z3_ROOT:-/opt/z3-4.8.9}" \
  -DYICES2_HOME=/opt/yices-2.6.1 \
  -DCMAKE_INSTALL_PREFIX=run \
  -DCMAKE_CXX_COMPILER=clang++-${LLVM_VERSION} \
  -DCMAKE_C_COMPILER=clang-${LLVM_VERSION} \
  -DCMAKE_C_COMPILER_LAUNCHER=ccache \
  -DCMAKE_CXX_COMPILER_LAUNCHER=ccache \
  -DSEA_ENABLE_LLD=ON \
  -DCPACK_GENERATOR="TGZ" \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON \
  -DWITH_CLAM=OFF \
  "${BITWUZLA_CMAKE[@]}"

# `extra` clones the third-party projects; re-run cmake to pick them up.
cmake --build . --target extra
cmake ..
cmake --build . --target install
cmake --build . --target units_z3
cmake --build . --target units_yices2
cmake --build . --target test_type_checker
cmake --build . --target test_hex_dump
cmake --build . --target package

if [ -n "$BITWUZLA_VERSION" ]; then
  # fail unless the installed seahorn has this Bitwuzla linked in, and loads
  # Bitwuzla, GMP and MPFR from the prefix (Ubuntu's are older)
  run/bin/seahorn --version | grep -F "Bitwuzla version $BITWUZLA_VERSION"
  ldd run/bin/seahorn | grep -E 'bitwuzla|gmp|mpfr' | tee /tmp/bitwuzla-ldd.txt
  grep -q libbitwuzla /tmp/bitwuzla-ldd.txt
  if grep -vF "=> $BITWUZLA_PREFIX/lib/" /tmp/bitwuzla-ldd.txt; then
    echo "build_seahorn.sh: the libraries above are not from $BITWUZLA_PREFIX/lib" >&2
    exit 1
  fi
  cmake --build . --target units_bitwuzla
fi

for u in ${UNITS:-z3 yices2 type_checker}; do
  units/units_$u
done

echo "==== ccache statistics ===="
ccache --show-stats || true
