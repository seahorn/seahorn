# Commit guidelines

We use [conventional commits](https://www.conventionalcommits.org/en/v1.0.0/) for commit messages and [clang-format ](https://clang.llvm.org/docs/ClangFormat.html)(llvm style) for C++ code.

## How to ensure your commits meet the guidelines

Install [precommit](https://pre-commit.com/) 

```shell
>pip3 install pre-commit
```

Install `golang`if not already present (needed for conform)

See if you have `golang`. E.g.

```shell
>go version
go version go1.14.2 linux/amd64
```

Install `clang-format` (needed for conform)

```shell
sudo apt-get install clang-format
```

Enable precommit inside root of local git repo

```
>pre-commit install
```

If you don't have it installed, you can install it using the [getgo tool](https://github.com/golang/tools/tree/master/cmd/getgo).

Install pre-commit into the `commit-msg` hook 

<!-- TODO commit-msg hook may not be needed. This requires more testing so not blocking checkin on this -->

```
 pre-commit install -t commit-msg
```

Everything is now setup. `seahorn` contains the following configuration files (you should not need to change them).

* `.pre-commit-config.yaml` - This is the configuration for pre-commit i.e. which checks to run e.g. `conform`, `clang-format`
* `.conform.yaml`- This is the configuration used by [conform](https://github.com/talos-systems/conform) to figure out which checks to enable e.g. conventional commits.

#### Run checks

You can manually run a check from within a repo using

```
>pre-commit run
```

Checks will automatically be run during `git commit`.