# SeaHorn #

![18093415-vector-illustration-of-seahorse-cartoon--coloring-book.jpg](https://bitbucket.org/repo/gngGo9/images/174701276-18093415-vector-illustration-of-seahorse-cartoon--coloring-book.jpg)

#About#

An LLVM based verification framework.

#Compilation#

* `cd seahorn ; mkdir build ; cd build`
* `cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=run ../ `
* (optional) `cmake --build . --target extra` to download extra packages
* `cmake --build .` to build dependencies (Z3 and LLVM)
* `cmake --build .` to build extra packages (llvm-ikos)
* `cmake --build .` to build seahorn
* `cmake --build . --target install` to install everything in `run` directory

SeaHorn and dependencies are installed in `build/run`

Optional components can be installed individually as well:
* (optional) download [dsa-seahorn](https://github.com/seahorn/dsa-seahorn): ``` git clone https://github.com/seahorn/dsa-seahorn.git ```
* (optional) download [ikos-llvm](https://github.com/seahorn/ikos-llvm): ``` git clone https://github.com/seahorn/ikos-llvm.git```
* (optional) download [llvm-seahorn](https://github.com/seahorn/llvm-seahorn): ``` git clone https://github.com/seahorn/llvm-seahorn.git```

Note that both [dsa-seahorn](https://github.com/seahorn/dsa-seahorn)
and [ikos-llvm](https://github.com/seahorn/ikos-llvm) are
optional. Nevertheless both are highly recommended. The former is
needed when reasoning about memory contents while the latter provides
inductive invariants using abstract interpretation techniques to the
rest of SeaHorn's backends.


#Usage#
TBD

#People#

* [Arie Gurfinkel](arieg.bitbucket.org)
* [Jorge Navas](http://ti.arc.nasa.gov/profile/jorge/)
* [Temesghen Kahsai](http://www.lememta.info/)

