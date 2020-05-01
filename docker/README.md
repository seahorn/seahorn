# Docker Images for SeaHorn

This directory contains scripts for building docker containers to compile and
run SeaHorn. These are mostly used by CI.

To get a docker distribution of this version of SeaHorn do:

```shell
$ docker pull seahorn/seahorn-llvm10:nightly
```

The instructions in this file are for developers only. If you are looking for a
docker distribution, go to DockerHub: https://hub.docker.com/u/seahorn

## SeaHorn Build Dependencies

This container contains all the third-party dependencies that are required for
building SeaHorn from sources. To build a container, run the following command
from the root of SeaHorn source tree:

```shell
$ docker build  -t seahorn/buildpack-deps-seahorn:bionic-llvm10 -f docker/buildpack-deps-seahorn.Dockerfile .
```

## Compiling SeaHorn

This container builds a distribution package of the current version of SeaHorn.
Run the following command from the *ROOT* of SeaHorn source tree:
```shell
$ docker build  -t seahorn/seahorn-builder:bionic-llvm10 -f docker/seahorn-builder.Dockerfile .
$ docker run -v $(pwd):/host --rm -it seahorn/seahorn-builder:bionic-llvm10 /bin/sh -c "cp build/*.tar.gz /host/"
```

## Distribution Container 

This container has the binary SeaHorn installed with all the necessary build
tools, but without any of the build by-products. This is the container used to
run tests in the CI. This is the container distributed to the users.

To build, run the following command in SeaHorn root. The command expects that
the distribution package is in the current directory

```shell
$ docker build  -t seahorn/seahorn-llvm10:latest -f docker/seahorn.Dockerfile .
$ docker run --rm -it seahorn/seahorn-llvm10:latest 
```

## Pushing a Container to DockerHub 
1. `export DOCKER_ID_USER=username`
2. `docker login`
5. `docker push`

## Cleaning after DockerHub

Docker generates many stale files. These should be cleaned after any extensive
docker command usage.

Some instructions: https://linuxize.com/post/how-to-remove-docker-images-containers-volumes-and-networks/

### Prune everything away
```
docker system prune
```

### Remove stopped containers
```
docker container prune
```

### Remove images
```
docker image prune
```

### Remove all unused images
```
docker image print -a
```
