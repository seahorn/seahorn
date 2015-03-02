# SeaHorn #

![18093415-vector-illustration-of-seahorse-cartoon--coloring-book.jpg](https://bitbucket.org/repo/gngGo9/images/174701276-18093415-vector-illustration-of-seahorse-cartoon--coloring-book.jpg)

#About#

An LLVM based verification framework.

#Compilation#

* (optional) download [dsa-seahorn](https://github.com/seahorn/dsa-seahorn): ``` git clone https://github.com/seahorn/dsa-seahorn.git ```
* (optional) download [ikos-llvm](https://github.com/seahorn/ikos-llvm): ``` git clone https://github.com/seahorn/ikos-llvm.git```
* ``` mkdir build ```
* ``` cd build ```
* ``` cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=run ../ ``` 
* ```cmake --build .``` to build llvm and z3 dependencies
* ```cmake ../``` to configure with dependencies from the previous step
* (optional) ```cmake --build . --target ikos-core```to build ikos-core dependency
* (optional) ```cmake ../``` to configure with ikos enabled
* ```cmake --build . --target install``` to build and install

SeaHorn and dependencies are installed in ```build/run```

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

