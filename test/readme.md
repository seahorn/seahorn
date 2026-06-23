This directory contains Seahorn's regression test suite. It uses
LLVM's [lit](http://llvm.org/docs/CommandGuide/lit.html) testing tool.


# Installing lit and filecheck

```
$ apt-get install python-pip
$ pip install lit
$ pip install filecheck
```

# Running the tests

```
$ cd <BUILD_DIR> ; cmake --build . --target test-simple
```
