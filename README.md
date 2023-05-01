[![seahorn](https://seahorn.github.io/images/seahorn-logo.png)](https://seahorn.github.io)


![os](https://img.shields.io/badge/os-linux-orange?logo=linux)
![os](https://img.shields.io/badge/os-macos-silver?logo=apple)
[![Nighly Build](https://img.shields.io/github/actions/workflow/status/seahorn/seahorn/seahorn-docker.yml)](https://github.com/seahorn/seahorn/actions/workflows/seahorn-docker.yml)
[![codecov](https://codecov.io/gh/seahorn/seahorn/branch/master/graph/badge.svg)](https://codecov.io/gh/seahorn/seahorn)
[![gitter](https://badges.gitter.im/seahorn/seahorn.svg)](https://gitter.im/seahorn/seahorn?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)

<!-- 

[![Azure DevOps builds (branch)](https://img.shields.io/azure-devops/build/seahorn/seahorn/1/dev10?label=azure-build)](https://dev.azure.com/seahorn/seahorn/_build)

-->

# About #

[SeaHorn][seahorn-web] is an automated analysis framework for
 LLVM-based languages. This version compiles against LLVM 14.

Some of the supported features are
 
 * Abstract Interpretation-based static analysis
 * Unification-based Context-Sensitive pointer analysis
 * SMT-based Bounded Model Checking (i.e., symbolic execution)
 * CHC-based Software Model Checking (i.e., invariant inference)
 * Executable counterexamples (i.e., no reports, just bugs!)
 
SeaHorn is developed primarily as a framework for conducting research in
automated verification. The frameworks provides many components that can be put
together in a variety of ways. However, it is not an "out-of-the-box" static
analysis tool.

Many analysis tools and examples are provided with the framework. We are
constantly looking for new applications and provide support to new users. For
more information on what is happening, check our (infrequently updated)
[blog][seahorn-blog].

## License 

[SeaHorn][seahorn-web] is distributed under a modified BSD license. See
 [license.txt](license.txt) for details.
 
# Introduction

[![Demo](https://asciinema.org/a/261355.svg)](https://asciinema.org/a/261355)
---

SeaHorn provides a python script called `sea` to interact with
users. Given a C program annotated with assertions, users just need to
type: `sea pf file.c`

The result of `sea-pf` is `unsat` if all assertions hold, an `sat` if any of the
assertions are violated.

The option `pf` tells SeaHorn to translate `file.c` into LLVM
bitcode, generate a set of verification conditions (VCs), and
finally, solve them. The main back-end solver
is [spacer](https://github.com/Z3Prover/z3/tree/master/src/muz/spacer).


The command `pf` provides, among others, the following options:

- `--show-invars`: display computed invariants if answer was `unsat`.

- `--cex=FILE` : stores a counter-example in `FILE` if answer was `sat`.

- `-g` : compiles with debug information for more trackable
  counterexamples.

- `--step=large`: large-step encoding. Each transition relation
corresponds to a loop-free fragments.

- `--step=small`: small-step encoding. Each transition relation
  corresponds to a basic block.

- `--track=reg` : model (integer) registers only.

- `--track=ptr` : model registers and pointers (but not memory content)

- `--track=mem`: model both scalars, pointers, and memory contents

- `--inline` : inlines the program before verification

- `--crab` : inject invariants in `spacer` generated by the Crab
  abstract-interpretation-based
  tool. Read
  [here](https://github.com/seahorn/crab-llvm/wiki/ClamOptions) for
  details about all Crab options (prefix `--crab`). You can see which
  invariants are inferred by Crab by typing option `--log=crab`.

- `--bmc`: use BMC engine.

`sea pf` is a pipeline that runs multiple commands. Individual parts
of the pipeline can be run separately as well:

1. `sea fe file.c -o file.bc`: SeaHorn frontend translates a C program
  into optimized LLVM bitcode including mixed-semantics
  transformation.

2. `sea horn file.bc -o file.smt2`: SeaHorn generates the verification
  conditions from `file.bc` and outputs them into SMT-LIB v2 format. Users
  can choose between different encoding styles with several levels of
  precision by adding:

   - `--step={small,large,fsmall,flarge}` where `small` is small step
      encoding, `large` is block-large encoding, `fsmall` is small
      step encoding producing flat Horn clauses (i.e., it generates a
      transition system with only one predicate), and `flarge`:
      block-large encoding producing flat Horn clauses.

   - `--track={reg,ptr,mem}` where `reg` only models integer
      scalars, `ptr` models `reg` and pointer addresses, and `mem`
      models `ptr` and memory contents.

3. `sea smt file.c -o file.smt2`: Generates CHC in SMT-LIB2 format. Is
   an alias for `sea fe` followed by `sea horn`. The command `sea pf`
   is an alias for `sea smt --prove`.

4.  `sea clp file.c -o file.clp`: Generates CHC in CLP format.

5. `sea lfe file.c -o file.ll` : runs the legacy front-end

To see all the commands, type `sea --help`. To see options for each
individual command CMD (e.g, `horn`), type `sea CMD --help` (e.g.,
`sea horn --help`).

## Static Analysis with Abstract Interpretation 

### Inference of Inductive Invariants using Crab 

SeaHorn does not use Crab by default. To enable Crab, add the option `--crab`
to the `sea` command.

The abstract interpreter is by default intra-procedural and it uses
the [Zones](https://jorgenavas.github.io/papers/zones-SAS16.pdf)
domain as the numerical abstract domain. These default options should
be enough for normal users.  For developers, if you want to use other
abstract domains you need to:

1. Compile with `cmake` options `-DCRAB_USE_LDD=ON -DCRAB_USE_ELINA=ON`
2. Run `sea` with option `--crab-dom=DOM` where `DOM` can be:
   - `int` for intervals
   - `term-int` for intervals with uninterpreted functions
   - `boxes`: for disjunctive intervals 
   - `oct` for octagons 
   - `pk` for polyhedra 

To use the crab inter-procedural analysis you need to run `sea` with
option `--crab-inter`

By default, the abstract interpreter only reasons about scalar
variables (i.e., LLVM registers). Run `sea` with the options
`--crab-track=mem --crab-singleton-aliases=true` to reason about
memory contents.

### How to use Invariants generated by Crab in Spacer 

Crab is mostly path-insensitive while Spacer, our Horn clause solver,
is path-sensitive. Although path-insensitive analyses are more
efficient, path-sensitivity is typically required to prove the
property of interest. This motivates our decision of running first
Crab (if option `--crab`) and then pass the generated invariants to
Spacer. There are currently two ways for Spacer to use the invariants
generated by Crab. The `sea` option `--horn-use-invs=VAL` tells
`spacer` how to use those invariants:

- If `VAL` is equal to `bg` then invariants are only used to help
  `spacer` in proving a lemma is inductive.
- If `VAL` is equal to `always` then the behavior is similar to `bg`
  but in addition invariants are also used to help `spacer` to block a
  counterexample.

The default value is `bg`. Of course, if Crab can prove the program is
safe then Spacer does not incur in any extra cost.

## Property Specification

Properties are assumed to be assertions. SeaHorn provides a static assertion command `sassert`, as illustrated in the following example
``` c 
/* verification command: sea pf --horn-stats test.c */
#include "seahorn/seahorn.h"
extern int nd();

int main(void) {
    int k = 1;
    int i = 1;
    int j = 0;
    int n = nd();
    while (i < n) {
        j = 0;
        while (j < i) {
            k += (i - j);
            j++;
        }
        i++;
    }
    sassert(k >= n);
}
```

Internally, SeaHorn follows [SV-COMP](http://sv-comp.sosy-lab.org) convention of
encoding error locations by a call to the designated error function
`__VERIFIER_error()`. SeaHorn returns `unsat` when `__VERIFIER_error()` is
unreachable, and the program is considered safe. SeaHorn returns `sat` when
`__VERIFIER_error()` is reachable and the program is unsafe. `sassert()` method
is defined in `seahorn/seahorn.h`.

## Inspect Code 

Apart from proving properties or producing counterexamples, it is
sometimes useful to inspect the code under analysis to get an idea of
its complexity. For this, SeaHorn provides a command `sea
inspect`. For instance, given a C program `ex.c` type:

	sea inspect ex.c --sea-dsa=cs+t --mem-dot 
	 
The option `--sea-dsa=cs+t` enables the new context-, type-sensitive sea-dsa
analysis described in
[FMCAD19](https://jorgenavas.github.io/papers/tea-dsa-fmcad19.pdf). This command
generates a `FUN.mem.dot` file for each function `FUN` in the input 
program. To visualize the graph of the main function, use web graphivz interface, or the following commands:

```shell
$ dot -Tpdf main.mem.dot -o main.mem.pdf
```

More details on the memory graphs is in the SeaDsa repository: 
[here](https://github.com/seahorn/sea-dsa#visualizing-memory-graphs-and-complete-call-graphs). 

Use `sea inspect --help` to see all options. Currently, the available options
are:

- `sea inspect --profiler` prints the number of functions, basic blocks,
  loops, etc.
- `sea inspect --mem-callgraph-dot` prints to `dot` format the call
  graph constructed by SeaDsa.
- `sea inspect --mem-callgraph-stats` prints to standard output some
  statstics about the call graph construction done by SeaDsa.
- `sea inspect --mem-smc-stats` prints the number of memory accesses
  that can be proven safe by SeaDsa.

# Installation

The easiest way to get started with SeaHorn is via a docker distribution. 

```shell
$ docker pull seahorn/seahorn-llvm10:nightly
$ docker run --rm -it seahorn/seahorn-llvm10:nightly
```

Start with exploring what the `sea` command can do:
```shell
$ sea --help
$ sea pf --help
```

The `nightly` tag is automatically refreshed daily and contains the latest
development version. We maintain all other tags (that require manual update)
infrequently. Check the dates on DockerHub and log an issue on GitHub if they
are too stale.

Additional examples and configuration options are on the [blog][seahorn-blog].
The blog is updated infrequently. In particular, options change, features are
phased out, new things are added. If you find problems in the blog, let us know.
We at least will update the blog post to indicate that it is not expected to
work with the latest version of the code.


# Developer's Zone

The information from this point on is for developers only. If you would like to
contribute to SeaHorn, build your own tools based on it, or just interested in
how it works inside, keep reading.

## Compilation Instructions 

SeaHorn requires [LLVM](https://llvm.org), [Z3](https://github.com/Z3Prover/z3),
and [boost](https://www.boost.org). The exact versions of the libraries keep
changing, but cmake craft is used to check that right version is available.

To specify a specific version of any of the dependencies, use the usual
[`<PackageName>_ROOT`](https://cmake.org/cmake/help/latest/variable/PackageName_ROOT.html)
and/or `<PackageName>_DIR` (see
[find_package()](https://cmake.org/cmake/help/latest/command/find_package.html)
for details) cmake variables.

SeaHorn is broken into multiple components that live in different repositories
(under SeaHorn organization). The build process automatically checks out
everything as necessary. For current build instructions, check the CI scripts.

These are the generic steps. Do **NOT** use them. Read on for a better way:
1. `cd seahorn ; mkdir build ; cd build` (The build directory can also be
   outside the source directory.)
1. `cmake -DCMAKE_INSTALL_PREFIX=run ../ ` (Install is **required!**)
1. `cmake --build . --target extra && cmake ..` (clones components that live elsewhere)
1. `cmake --build . --target crab && cmake ..` (clones crab library) 
1. `cmake --build . --target install` (build and install everything under `run`)
1. `cmake --build . --target test-all` (run tests)

**Note**: **install** target is required for tests to work!

## Better Compilation Instructions

For an enhanced development experience:
1. Use `clang`
1. On Linux, use `lld` linker
1. Include debug symbols in Release builds
1. Use [Ninja](https://ninja-build.org/)
1. Export [`compile_commands.json`](https://clang.llvm.org/docs/JSONCompilationDatabase.html)

On Linux, we suggest the following `cmake` configuration:
```
$ cd build
$ cmake -DCMAKE_INSTALL_PREFIX=run \
      -DCMAKE_BUILD_TYPE=RelWithDebInfo \
      -DCMAKE_CXX_COMPILER="clang++-14" \
      -DCMAKE_C_COMPILER="clang-14" \
      -DSEA_ENABLE_LLD=ON  \
      -DCMAKE_EXPORT_COMPILE_COMMANDS=1 \
      ../ \
      -DZ3_ROOT=<Z3_ROOT> \
      -DLLVM_DIR=<LLMV_CMAKE_DIR> \
      -GNinja
$ (cd .. && ln -sf build/compile_commands.json .)
```
where `<Z3_ROOT` is a directory containing Z3 binary distribution, and `LLMV_CMAKE_DIR` is directory containing `LLVMConfig.cmake`. 

Other legal options for `CMAKE_BUILD_TYPE` are `Debug` and `Coverage`. Note that
the `CMAKE_BUILD_TYPE` must be compatible with the one used to compile `LLVM`.
In particular, you will need a `Debug` build of LLVM to compile `SeaHorn` in
`Debug** mode. Make sure you have plenty of patience, disk space, and time if you
decide to go this route.

## Compiling on a Mac

**Do not include `-DSEA_ENABLE_LLD=ON`**. The default compiler is clang, so you
might not need to set it explicitly.


## The **EXTRA** Target 

SeaHorn provides several components that are automatically cloned and installed via the `extra`
target. These components can be used by other projects outside of
SeaHorn.

* [sea-dsa](https://github.com/seahorn/sea-dsa): `git clone https://github.com/seahorn/sea-dsa.git`

  `sea-dsa` is a new DSA-based heap analysis. Unlike `llvm-dsa`,
  `sea-dsa` is context-sensitive and therefore, a finer-grained
  partition of the heap can be generated in presence of function
  calls.

* [clam](https://github.com/seahorn/crab-llvm): `git clone https://github.com/seahorn/crab-llvm.git`

  `clam` provides inductive invariants using abstract interpretation
  techniques to the rest of SeaHorn's backends.

* [llvm-seahorn](https://github.com/seahorn/llvm-seahorn): `git clone https://github.com/seahorn/llvm-seahorn.git`

  `llvm-seahorn` provides tailored-to-verification versions of
  `InstCombine` and `IndVarSimplify` LLVM passes as well as a LLVM
  pass to convert undefined values into nondeterministic calls, among
  other things.

SeaHorn doesn't come with its own version of Clang and expects to find it
either in the build directory (`run/bin`) or in PATH. Make sure that the
version of Clang matches the version of LLVM that was used to compile 
SeaHorn (currently LLVM14). The easiest way to provide the right version of 
Clang is to download it from [llvm.org](http://releases.llvm.org/download.html),
unpact it somewhere and create a symbolic link to `clang` and `clang++`
in `run/bin`.

```shell
$ cd seahorn/build/run/bin
$ ln -s <CLANG_ROOT>/bin/clang clang
$ ln -s <CLANG_ROOT>/bin/clang++ clang++
```
where `<CLANG_ROOT>` is the location at which Clang was unpacked.

## Tests 

Testing infrastructure depends on several Python packages. These have their own
dependencies. If you cannot figure them out, use docker instead.

```shell
$ pip install lit OutputCheck networkx pygraphviz
```

## Coverage 

We can use `gcov` and `lcov` to generate test coverage information for SeaHorn.
To build with coverage enabled, we need to run build under a different directory
and set `CMAKE_BUILD_TYPE` to `Coverage` during cmake configuration.

Example steps for generating coverage report for the `test-opsem` target:
1. `mkdir coverage; cd coverage`  create and enter coverage build directory
2. `cmake -DCMAKE_BUILD_TYPE=Coverage <other flags as you wish> ../`
3. Complete the build as usual
4. `cmake --build . --target test-opsem` Run OpSem tests, now `.gcda` and
`.gcno` files should be created in the corresponding `CMakeFiles` directories
5. `lcov -c --directory lib/seahorn/CMakeFiles/seahorn.LIB.dir/ -o coverage.info` collect coverage data from desired module,
if `clang` is used as the compiler instead of `gcc`, create a bash script `llvm-gcov.sh`:
```shell
#!/bin/bash
exec llvm-cov gcov "$@"
```
```shell 
$ chmod +x llvm-gcov.sh
```
then append `--gcov-tool <path_to_wrapper_script>/llvm-gcov.sh` to the `lcov -c ...` command.
6. extract data from desired directories and generate html report:
```shell
lcov --extract coverage.info "*/lib/seahorn/*" -o lib.info
lcov --extract coverage.info "*/include/seahorn/*" -o header.info
cat header.info lib.info > all.info
genhtml all.info --output-directory coverage_report
```
then open `coverage_report/index.html` in browser to view the coverage report

Also see `scripts/coverage` for scripts used by the CI. Coverage report for nightly builds is available at [codecov](https://codecov.io/gh/seahorn/seahorn)

## Code indexing 

[Compilation database](http://clang.llvm.org/docs/JSONCompilationDatabase.html)
for the seahorn project and all its sub-projects is generated using
`-DCMAKE_EXPORT_COMPILE_COMMANDS=ON` option for `cmake`.

An easy way to get code indexing to work with with compilation database support
is to link the `compilation_database.json` file into the main project directory
and follow instructions specific to your editor.

- Clion -- https://www.jetbrains.com/help/clion/compilation-database.html
- Vim (YouCompleteMe) -- [instructions](https://github.com/Valloric/YouCompleteMe#option-1-use-a-compilation-database)
- Emacs -- use `lsp-ui` with `clangd` which are available in [spacemacs](https://github.com/syl20bnr/spacemacs/tree/develop) develop branch

## Remote Configuration for CLion
For a detailed guide for a remote workflow with CLion check 
[Clion-configuration](CLion-configuration.md).

## Remote Configuration for Emacs (and other Editors)

Use our fork of [mainframer](https://github.com/agurfinkel/mainframer). Don't
miss the example
[configuration](https://github.com/agurfinkel/mainframer/tree/master/samples/ag/.mainframer).

# Contributors

* [Arie Gurfinkel](https://arieg.bitbucket.org/)
* [Jorge Navas](https://jorgenavas.github.io/)
* [Temesghen Kahsai](http://www.lememta.info/)
* [Jakub Kuderski](https://github.com/kuhar)
* [Nham Le](https://github.com/nhamlv-55)
* [Charles Lei](https://github.com/mrthefakeperson)
* [Xiang Zhou](https://github.com/danblitzhou)
* [Siddharth Priya](https://github.com/priyasiddharth)
* [Isabel Garcia-Contreras](https://igcontreras.github.io/)
* [Yusen Su](https://github.com/LinerSu)
* EMAIL ME IF YOUR NAME SHOULD BE HERE

[seahorn-web]: https://seahorn.github.io
[seahorn-blog]: https://seahorn.github.io/blog
