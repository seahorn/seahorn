<p align=center><a href="https://seahorn.github.io"><img src="https://seahorn.github.io/images/seahorn-logo.png" alt="seahorn" width="200px" height="200px"/></a></p>

<table>
  <tr>
    <th>Windows</th><th>Ubuntu</th><th>OS X</th> <th>Chat with us</th>
  </tr>
    <td>TBD</td>
    <td><a href="https://travis-ci.org/seahorn/seahorn"><img src="https://travis-ci.org/seahorn/seahorn.svg?branch=master" title="Ubuntu 12.04 LTS 64bit, g++-4.8"/></a></td>
    <td>TBD</td>
    <td>[![Gitter](https://badges.gitter.im/seahorn/seahorn.svg)](https://gitter.im/seahorn/seahorn?utm_source=badge&utm_medium=badge&utm_campaign=pr-badge)</td>
  </tr>
</table>



#About#

SeaHorn is an automated analysis framework for LLVM-based languages.

#License#
SeaHorn is distributed under a modified BSD license. See [license.txt](license.txt) for details.

#Installation#

* `cd seahorn ; mkdir build ; cd build`
* `cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=run ../ `
* (optional) `cmake --build . --target extra` to download extra packages
* `cmake --build .` to build dependencies (Z3 and LLVM)
* (optional) `cmake --build .` to build extra packages (crab-llvm)
* `cmake --build .` to build seahorn
* `cmake --build . --target install` to install everything in `run` directory

SeaHorn and dependencies are installed in `build/run`

Optional components can be installed individually as well:

* [dsa-seahorn](https://github.com/seahorn/dsa-seahorn): ``` git clone https://github.com/seahorn/dsa-seahorn.git ```

* [crab-llvm](https://github.com/seahorn/crab-llvm): ``` git clone https://github.com/seahorn/crab-llvm.git```

* [llvm-seahorn](https://github.com/seahorn/llvm-seahorn): ``` git clone https://github.com/seahorn/llvm-seahorn.git```

Note that both [dsa-seahorn](https://github.com/seahorn/dsa-seahorn)
and [crab-llvm](https://github.com/seahorn/crab-llvm) are
optional. Nevertheless both are highly recommended. The former is
needed when reasoning about memory contents while the latter provides
inductive invariants using abstract interpretation techniques to the
rest of SeaHorn's backends.

___

**Latest news**: due to some unsolved licensing issues `crab-llvm` is
temporary not publicly available. Please, if this impacts your current
project do not hesitate to contact us at <seahorn@aguga.net>.

#Usage#

SeaHorn provides a python script called `sea` to interact with
users. Given a C program annotated with assertions, users just need to
type: `sea pf file.c`

This will output `unsat` if all assertions hold or otherwise `sat` if
any of the assertions is violated. The option `pf` tells SeaHorn to
translate `file.c` into LLVM bitecode, generate a set of verification
conditions (VCs), and finally, solve them. This command uses as main
default options:

- `--step=large`: large-step encoding. Each step corresponds to a
loop-free program block.

- `--step=small`: small-step encoding. Each step corresponds to a
  basic block.

- `--track=mem`: model both scalars, pointers, and memory contents

- `--track=ptr` : model registers and pointers (but not memory content)

- `--track=reg` : model registers only

- `--inline` : inlines the program before verification

- `--cex=FILE` : stores a counter-example in `FILE`

- `--crab` : generates invariants using the Crab
  abstract-interpretation-based tool. Read
  [here](https://github.com/seahorn/crab-llvm/tree/master#usage) for
  details about Crab options. **This option is currently disabled.**

- `-g` : compiles with debug information for more trackable
  counterexamples.

`sea pf` is a pipeline that runs multiple commands. Individual parts
of the pipeline can be ran separately as well:

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

To see all the options, type `sea --help`.

##Annotating C programs##

This is an example of a C program annotated with a safety property:
``` c
    /* verification command: sea pf --horn-stats test.c */
    #include "seahorn/seahorn.h"
    int nd();

    int main(void){
      int k=1;
      int i=1;
      int j=0;
      int n = nd();
      while(i<n) {
        j=0;
        while(j<i) {
          k += (i-j);
          j++;
        }
        i++;
      }
      sassert(k>=n);
    }

```
SeaHorn follows [SV-COMP][svcomp] convention of encoding error locations by a call
to the designated error function
`__VERIFIER_error()`. SeaHorn returns `unsat` when `__VERIFIER_error()`
is unreachable, and the program is considered safe. SeaHorn returns `sat`
when `__VERIFIER_error()` is reachable and the
program is unsafe. `sassert()` method is defined in `seahorn/seahorn.h` which can be found in `seahorn/share`.

[svcomp]: (http://sv-comp.sosy-lab.org)

#People#

* [Arie Gurfinkel](arieg.bitbucket.org)
* [Jorge Navas](http://ti.arc.nasa.gov/profile/jorge/)
* [Temesghen Kahsai](http://www.lememta.info/)
