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

# Known limitations

Some tests document a case SeaHorn cannot solve yet (for example, Spacer
does not converge). Such a test is bounded so it terminates quickly
(e.g. `--max-depth`), checks the result SeaHorn gives today (usually
`unknown`), and carries a line naming the result we want and why we do
not get it:

```
// KNOWN-LIMITATION: want unsat; <reason>
```

List them with `grep -rn KNOWN-LIMITATION test/`. When a limitation is
fixed, the test starts failing; update its CHECK to the wanted result
and drop the marker.
