# Examples for harnesses with memory

This directory contains simple tests for harness generation in the
presence of external memory. Each example (unless indicated otherwise)
results in SAT (counterexample) answer from SeaHorn.

To simplify debugging, a macro `BASE_PTR`, defined in `memcex.h`, is
used to assign non-deterministic pointers an easy to spot
address. This can be disabled for harness generation. The harness
should be generated independently of the definition of `BASE_PTR`
macro.

The command line option used to run sea script is

```
sea pf -O0 testXXX.c --horn-stats -g --cex=/tmp/harness.ll --log=cex --oll=/tmp/out.ll --dsa=sea-cs   2>&1 | tee /tmp/log
```

# Contributors

Arie Gurfinkel
