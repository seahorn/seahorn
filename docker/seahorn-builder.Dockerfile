# SeaHorn builder image that builds binary SeaHorn release package
# Primarily used by the CI
# Arguments:
#  - TRAVIS:     true (optional, for use on Travis only)
FROM seahorn/buildpack-deps-seahorn:bionic-llvm10

ARG TRAVIS

# Assume that docker-build is ran in the top-level SeaHorn directory
COPY . /seahorn
# Re-create the build directory that might have been present in the source tree
RUN rm -rf /seahorn/build /seahorn/debug /seahorn/release && \
  mkdir /seahorn/build && \
# Remove any third-party dependencies that build process clones
  rm -rf /seahorn/clam /seahorn/sea-dsa /seahorn/llvm-seahorn
WORKDIR /seahorn/build

# Build configuration
RUN cmake .. -GNinja \
  -DCMAKE_BUILD_TYPE=RelWithDebInfo \
  -DZ3_ROOT=/opt/z3-4.8.7 \
  -DYICES2_HOME=/opt/yices-2.6.1 \
  -DCMAKE_INSTALL_PREFIX=run \
  -DCMAKE_CXX_COMPILER=clang++-10 \
  -DCMAKE_C_COMPILER=clang-10 \
  -DSEA_ENABLE_LLD=ON \
  -DCPACK_GENERATOR="TGZ" \
  -DCMAKE_EXPORT_COMPILE_COMMANDS=ON && \
  cmake --build . --target extra  && cmake .. && \
  cmake --build . --target crab  && cmake .. && \
  cmake --build . --target install && \
  cmake --build . --target units_z3 && \
  cmake --build . --target units_yices2 && \
  cmake --build . --target package && \
  units/units_z3 && \
  units/units_yices2

ENV PATH "/seahorn/build/run/bin:$PATH"
WORKDIR /seahorn
