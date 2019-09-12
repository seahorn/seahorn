<p align=center><a href="https://seahorn.github.io"><img src="https://seahorn.github.io/images/seahorn-logo.png" alt="seahorn" width="200px" height="200px"/></a></p>

<table>
  <tr>
    <th>Windows</th><th>Ubuntu</th><th>OS X</th><th>Chat with us</th>
  </tr>
    <td>TBD</td>
    <td><a href="https://travis-ci.org/seahorn/seahorn"><img src="https://travis-ci.org/seahorn/seahorn.svg?branch=deep-dev-5.0" title="Ubuntu 12.04 LTS 64bit, g++-5"/></a></td>
    <td>TBD</td>
    <td><a href="https://gitter.im/seahorn/seahorn?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge"><img src="https://badges.gitter.im/seahorn/seahorn.svg" title="Gitter"/></a></td>
  </tr>
</table>

# About #

<a href="http://seahorn.github.io/">SeaHorn</a> is an automated analysis framework for LLVM-based languages. This version supports LLVM 5.0.

# License #

<a href="http://seahorn.github.io/">SeaHorn</a> is distributed under a modified BSD license. See [license.txt](license.txt) for details.

# Installation #

1. `cd seahorn ; mkdir build ; cd build` (The build directory can also be outside the source directory.)
1. `cmake -DCMAKE_INSTALL_PREFIX=run ../ `
  (Add `-GNinja` to use the [Ninja](https://ninja-build.org/) generator instead of the default one.
   Build types (Release, Debug) can be set with `-DCMAKE_BUILD_TYPE=<TYPE>`.)
1. `cmake --build .` to build dependencies (Z3 and LLVM)
1. `cmake --build . --target extra && cmake ..` to download extra packages
1. `cmake --build . --target crab && cmake ..` to configure crab-llvm (if `extra` target was run)
1. `cmake --build . --target install` to build seahorn and install everything in `run` directory

_Note that the *install* target is required!_

The install target installs SeaHorn all of it dependencies under `build/run`.
The main executable is `build/run/bin/sea`.

## Compiling with Clang on Linux

Usually, compilation time with clang and lld linker are faster than
other options on Linux. The magic cmake configuration line is
something like the following:

```
 cmake -DCMAKE_INSTALL_PREFIX=run -DCMAKE_BUILD_TYPE="Release" -DCMAKE_CXX_COMPILER="clang++-8" -DCMAKE_C_COMPILER="clang-8" -DSEA_ENABLE_LLD="ON" -GNinja -DCMAKE_EXPORT_COMPILE_COMMANDS=1 ../
```
This command should be run instead of the cmake command *2.* in the installation instructions above.

SeaHorn provides several components that are automatically cloned and installed via the `extra`
target. These components can be used by other projects outside of
SeaHorn.

* [llvm-dsa](https://github.com/seahorn/llvm-dsa): `git clone https://github.com/seahorn/llvm-dsa.git`

  `llvm-dsa` is the legacy DSA implementation
  from [PoolAlloc](https://llvm.org/svn/llvm-project/poolalloc/). DSA
  is a heap analysis used by SeaHorn to disambiguate the heap.

* [sea-dsa](https://github.com/seahorn/sea-dsa): `git clone https://github.com/seahorn/sea-dsa.git`

  `sea-dsa` is a new DSA-based heap analysis. Unlike `llvm-dsa`,
  `sea-dsa` is context-sensitive and therefore, a finer-grained
  partition of the heap can be generated in presence of function
  calls.

* [crab-llvm](https://github.com/seahorn/crab-llvm): `git clone https://github.com/seahorn/crab-llvm.git`

  `crab-llvm` provides inductive invariants using abstract
  interpretation techniques to the rest of SeaHorn's backends.

* [llvm-seahorn](https://github.com/seahorn/llvm-seahorn): `git clone https://github.com/seahorn/llvm-seahorn.git`

  `llvm-seahorn` provides tailored-to-verification versions of
  `InstCombine` and `IndVarSimplify` LLVM passes as well as a LLVM
  pass to convert undefined values into nondeterministic calls, among
  other things.

SeaHorn doesn't come with its own version of Clang and expects to find it
either in the build directory (`run/bin`) or in PATH. Make sure that the
version of Clang matches the version of LLVM that comes with SeaHorn
(currently 5.0). The easiest way to provide the right version of Clang is
to download it from [llvm.org](http://releases.llvm.org/download.html),
unpact it somewhere and create a symbolic link to `clang` and `clang++`
in `run/bin`.
```
cd seahorn/build/run/bin
ln -s place_where_you_unpacked_clang/bin/clang clang
ln -s place_where_you_unpacked_clang/bin/clang++ clang++
```

# Test #

Running tests require several python packages:

``` shell
pip install lit OutputCheck
easy_install networkx
apt-get install libgraphviz-dev
easy_install pygraphviz

```


Tests can be run using:

``` shell
$ export SEAHORN=<install_dir>/bin/sea
$ cmake --build . --target test-all
```

# Coverage #
We can use `gcov` and `lcov` to generate test coverage information for SeaHorn. To build with coverage enabled,
we need to run build under a different directory and set `CMAKE_BUILD_TYPE` to `Coverage` during cmake configuration.

Example steps for `opsem` tests coverage:
1. `mkdir coverage; cd coverage`  create and enter coverage build directory
2. `cmake -DCMAKE_BUILD_TYPE=Coverage <other flags as you wish> ../`
configure cmake with `Coverage` build type, follow [Installation](https://github.com/seahorn/seahorn/tree/master#installation) or [Compiling with Clang on Linux
](https://github.com/seahorn/seahorn/tree/master#compiling-with-clang-on-linux) to set other flags
3. follow step 3 through 6 in *Installation* section to finish build
4. `cmake --build . --target test-opsem` Run OpSem tests, now .gcda and .gcno files should be created
under corresponding `CMakeFiles` directory

5. `lcov -c --directory lib/seahorn/CMakeFiles/seahorn.LIB.dir/ -o coverage.info` collect coverage data from desired module,
if `clang` is used as the compiler instead of `gcc`, create a bash script `llvm-gcov.sh`:
```shell script
#!/bin/bash
exec llvm-cov gcov "$@"
```
```shell script
$ chmod +x llvm-gcov.sh
```
then append `--gcov-tool <path_to_wrapper_script>/llvm-gcov.sh` to the `lcov -c ...` command.
6. extract data from desired directories and generate html report:
```shell script
lcov --extract coverage.info "*/lib/seahorn/*" -o lib.info
lcov --extract coverage.info "*/include/seahorn/*" -o header.info
cat header.info lib.info > all.info
genhtml all.info --output-directory coverage_report
```
then open `coverage_report/index.html` in browser to view the coverage report

# Code indexing for IDEs and editors #

[Compilation database](http://clang.llvm.org/docs/JSONCompilationDatabase.html) for the seahorn project and all its subprojects (e.g., llvm, z3, SeaDsa)
can be generated by adding `-DCMAKE_EXPORT_COMPILE_COMMANDS=1` to the first
cmake command presented in [Installation](Installation). This will produce an additional file
in the selected build directory -- `compile_commands.json`.

An easy way to get code indexing to work with with compilation database support
is to copy the `.json` file into the main project directory and follow
instructions specific to your editor:
* Clion -- https://www.jetbrains.com/help/clion/compilation-database.html
* Vim (YouCompleteMe) -- https://github.com/Valloric/YouCompleteMe#option-1-use-a-compilation-database
* Emacs (rtags) -- https://vxlabs.com/2016/04/11/step-by-step-guide-to-c-navigation-and-completion-with-emacs-and-the-clang-based-rtags/

## Remote Configuration for CLion
For a detailed guide for a remote workflow with CLion check 
[Clion-configuration](CLion-configuration.md).

# Usage #

### Demo ###
[![Demo](https://asciinema.org/a/261355.svg)](https://asciinema.org/a/261355)
---

SeaHorn provides a python script called `sea` to interact with
users. Given a C program annotated with assertions, users just need to
type: `sea pf file.c`

This will output `unsat` if all assertions hold or otherwise `sat` if
any of the assertions is violated.

The option `pf` tells SeaHorn to translate `file.c` into LLVM
bitecode, generate a set of verification conditions (VCs), and
finally, solve them. The main back-end solver
is [spacer](https://bitbucket.org/spacer/).


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
  [here](https://github.com/seahorn/crab-llvm/tree/master#crab-options) for
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

## Annotating C programs ##

This is an example of a C program annotated with a safety property:
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
SeaHorn follows [SV-COMP](http://sv-comp.sosy-lab.org) convention of
encoding error locations by a call to the designated error function
`__VERIFIER_error()`. SeaHorn returns `unsat` when
`__VERIFIER_error()` is unreachable, and the program is considered
safe. SeaHorn returns `sat` when `__VERIFIER_error()` is reachable and
the program is unsafe. `sassert()` method is defined in
`seahorn/seahorn.h`.

## Visualizing Memory Graphs ##

Consider a C program `ex.c`. Then type:

	sea inspect ex.c -sea-dsa=butd-cs -sea-dsa-type-aware --mem-dot 
	 
The options `-sea-dsa=butd-cs -sea-dsa-type-aware` enable the new
sea-dsa analysis implemented in our
FMCAD'19
[paper](https://jorgenavas.github.io/papers/tea-dsa-fmcad19.pdf). This
command will generate a `FUN.mem.dot` file for each function `FUN` in
the bitcode program.  For instance, to visualize the graph of the main
function type:

	dot -Tpdf main.mem.dot -o main.mem.pdf
	open main.mem.pdf  // replace with you favorite pdf viewer

Read this
[link](https://github.com/seahorn/sea-dsa#visualizing-memory-graphs-and-complete-call-graphs) for
more details.

## Building SeaHorn on Ubuntu 18.04 ##

The following packages are recommended to build SeaHorn on Ubuntu 18.04. Not
everything is necessary for all configurations, but it is simpler to have these
installed. This assumes that `clang` is used as a compiler as per-instructions
above.

```
sudo apt install cmake git build-essential ninja-build llvm-8 clang-8 clang-tools-8 lld-8 libboost-dev subversion g++-7-multilib gcc-multilib lib32stdc++7 libgmp-dev libgmpxx4ldbl libgraphviz-dev libncurses5-dev ncurses-doc
```

# Original Authors 

* [Arie Gurfinkel](https://arieg.bitbucket.org/)
* [Jorge Navas](https://jorgenavas.github.io/)
* [Temesghen Kahsai](http://www.lememta.info/)

# Contributors

* [Jakub Kuderski](https://github.com/kuhar)
* [Nham Le](https://github.com/nhamlv-55)
* [Charles Lei](https://github.com/mrthefakeperson)
