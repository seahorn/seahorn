# Building SeaHorn's dependencies with Docker

LLVM 3.8, z3/spacer, and boost 1.62 can be prebuilt using docker. E.g.
```shell
cd seahorn/deps/z3
docker build --build-arg UBUNTU=xenial --build-arg BUILD_TYPE=Release -t z3_xenial_rel .
docker run -v `pwd`:/host -it z3_xenial_rel
```
This will automatically create a z3.tar file in the current working directory.

For all the dependencies, the possible build arguments are:
- UBUNTU: trusty, xenial
- BUILD_TYPE: Release, Debug

Note that both `UBUNTU` and `BUILD_TYPE` are required arguments.
