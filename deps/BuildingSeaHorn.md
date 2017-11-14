# Building SeaHorn with Docker

To build SeaHorn with Docker:
```shell
cd seahorn/deps
docker build --build-arg UBUNTU=xenial --build-arg BUILD_TYPE=Release -t seahorn_xenial_rel .
docker run -v `pwd`:/host -it sehorn_xenial_rel
```
This will automatically download all dependencies and build SeaHorn under /seahorn/build.

SeaHorn's install directory is added to PATH, and a tarball with it is ready under the current working directory (on the host).

The possible build arguments are:
- UBUNTU: trusty, xenial
- BUILD_TYPE: Release, Debug

NOTE: Debug build type is not supported at the moment.

Note that both `UBUNTU` and `BUILD_TYPE` are required arguments.
