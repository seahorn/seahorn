# SeaHorn #

![18093415-vector-illustration-of-seahorse-cartoon--coloring-book.jpg](https://bitbucket.org/repo/gngGo9/images/174701276-18093415-vector-illustration-of-seahorse-cartoon--coloring-book.jpg)

#About#

An LLVM based verification framework.

#License#
SeaHorn is distributed under a modified BSD license. See [license.txt](license.txt) for details.

#Compilation#

* `cd seahorn ; mkdir build ; cd build`
* `cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=run ../ `
* (optional) `cmake --build . --target extra` to download extra packages
* `cmake --build .` to build dependencies (Z3 and LLVM)
* (optional) `cmake --build .` to build extra packages (llvm-ikos)
* `cmake --build .` to build seahorn
* `cmake --build . --target install` to install everything in `run` directory

SeaHorn and dependencies are installed in `build/run`

Optional components can be installed individually as well:
* [dsa-seahorn](https://github.com/seahorn/dsa-seahorn): ``` git clone https://github.com/seahorn/dsa-seahorn.git ```
* [ikos-llvm](https://github.com/seahorn/ikos-llvm): ``` git clone https://github.com/seahorn/ikos-llvm.git```
* [llvm-seahorn](https://github.com/seahorn/llvm-seahorn): ``` git clone https://github.com/seahorn/llvm-seahorn.git```

Note that both [dsa-seahorn](https://github.com/seahorn/dsa-seahorn)
and [ikos-llvm](https://github.com/seahorn/ikos-llvm) are
optional. Nevertheless both are highly recommended. The former is
needed when reasoning about memory contents while the latter provides
inductive invariants using abstract interpretation techniques to the
rest of SeaHorn's backends.


#Usage#

SeaHorn provides a python script called `sea` to interact with
users. Given a C program annotated with assertions, users just need to
type: `sea pf file.c`

This will output `unsat` if all assertions hold or otherwise `sat` if
any of the assertions is violated. The option `pf` tells SeaHorn to
translate `file.c` into LLVM bitecode, generate a set of verification
conditions (VCs), and finally, solve them. This command uses as main
default options:

- `--step=large`: block-large encoding

- `--horn-inter-proc`: inter-procedural encoding

- `--horn-sem-lvl=mem`: model both scalars, pointers, and memory contents

The above command can divided into several parts.

1. `sea fe file.c -o file.bc`: SeaHorn frontend translates a C program
  into optimized LLVM bitecode including mixed-semantics
  transformation.

2. `sea horn file.bc -o file.smt2`: SeaHorn generates the verification
  conditions from `file.bc` and outputs them into smt2 format. Users
  can choose between different encoding styles with several levels of
  precision by adding:

   - `--step={small,large,flarge}` where `small` is small step
      encoding, `large` is block-large encoding, and `flarge`:
      block-large encoding producing flat Horn clauses (i.e., it
      generates a transition system with only one predicate).

   - `--horn-sem-lvl={reg,ptr,mem}` where `reg` only models integer
      scalars, `ptr` models `reg` and pointer addresses, and `mem`
      models `ptr` and memory contents.

3. `sea smt file.smt2`: Seahorn tries to solve the VCs
   generated in 2.

4. `sea horn --solve file.bc`: performs steps 2 and 3 together.

   This command can be augmented with option `--horn-ikos` to add the
   Ikos abstract intepreter as another back-end solver.
      
5. `sea horn --solve --cex FILE file.bc`: as 4 but it outputs to
   `FILE` the counterexample if the answer is `sat`.

6.  `sea horn-clp file.bc -o file.clp`: similar to 2 but it generates
     the verification conditions in CLP format.

To see all the options, type `sea --help`.

##Annotating C programs##

This is an example of a C program annotated with a safety property:

    extern int __VERIFIER_NONDET();
    extern void __VERIFIER_error() __attribute__((noreturn));

    int main(){
      int x,y;
      x=1; y=0;
      while (__VERIFIER_NONDET())
      {
        x=x+y;
        y++;
      }
     if (!(x>=y)) __VERIFIER_error (); // assert (x>=y);
     return 0;
    }

SeaHorn tries to prove that the program location where is defined
`__VERIFIER_error()` is reachable. If SeaHorn returns `unsat` then the
location is unreachable, and the program is considered safe. If `sat`
then SeaHorn proves that the location is reachable, and therefore the
program is unsafe.


#People#

* [Arie Gurfinkel](arieg.bitbucket.org)
* [Jorge Navas](http://ti.arc.nasa.gov/profile/jorge/)
* [Temesghen Kahsai](http://www.lememta.info/)
