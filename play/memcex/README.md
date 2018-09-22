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

# Worked out example

Consider the counterexample computed for `test4.c`.

```
entry:
  mem_start_0 mem_start_0
  mem_end_0 mem_end_0
  %_0 [0xbeef0->42 | else -> 2]
  %_1 0xbeef0	[test4.c:6]
  p = _1
  %_2 true	[test4.c:8]
  %_3 0xbeef0
  %_4 true	[test4.c:9]
  %_5 0xbeef4	[test4.c:10]
  %_6 [0xbeef0->42 | 0xbeef4->43 | else -> 2]	[test4.c:10]
  %_7 0xbeef0	[test4.c:11]
  %_8 42	[test4.c:11]
  %_9 true	[test4.c:11]
_bb:
  %_11 0xbeef4	[test4.c:11]
  %_12 43	[test4.c:11]
  %_13 true	[test4.c:11]
_bb1:
verifier.error:
verifier.error.split:
```

There is one DSA node and one corresponding memory segment allocated
at `%_0`. The boundaries and the size of the segment are given by
`mem_start_0` and `mem_end_0`, respectively. Unfortunately, these are
left unconstrained in the current example, which needs to be fixed.

The initial content is given by the definition of `%_0`. In this case,
at address `0xbeef0` there is a value `42`, and every other address is
filled with `2`. Often the default value does not matter and the
counterexample can be simplified by replacing the default value with
`0`.

As another example, consider the case of `test7.c`

```
entry:
  mem_start_0 mem_start_0
  mem_end_0 mem_end_0
  %_0 [0xbeef0->42 | 0xbeef8->0xbeefc | else -> 1]
  mem_start_1 mem_start_1
  mem_end_1 mem_end_1
  %_1 [0xbeefc->526 | else -> 7]
  %_2 0xbeef0	[test7.c:6]
  p = _2
  %_3 true	[test7.c:8]
  %_4 0xbeef0
  %_5 true	[test7.c:9]
  %_6 0xbeef0	[test7.c:11]
  %_7 42	[test7.c:11]
  %_8 true	[test7.c:11]
_bb:
  %_10 0xbeef8	[test7.c:12]
  %_11 0xbeefc	[test7.c:12]
  %_12 false	[test7.c:12]
_bb2:
  %_14 0xbeef8	[test7.c:13]
  %_15 0xbeef8	[test7.c:13]
  %_16 0xbeefc	[test7.c:13]
  %_17 true	[test7.c:13]
  %_18 0xbeef8	[test7.c:14]
  %_19 0xbeefc	[test7.c:14]
  %_20 0xbef00	[test7.c:14]
  %_21 [0xbeefc->526 | 0xbef00->474 | else -> 7]	[test7.c:14]
  %_22 0xbeef8	[test7.c:15]
  %_23 0xbeefc	[test7.c:15]
  %_24 0xbeefc	[test7.c:15]
  %_25 526	[test7.c:15]
  %_26 true	[test7.c:15]
_bb3:
  %_28 0xbeef8	[test7.c:16]
  %_29 0xbeefc	[test7.c:16]
  %_30 0xbeefc	[test7.c:16]
  %_31 526	[test7.c:16]
  %_32 0xbef00	[test7.c:16]
  %_33 474	[test7.c:16]
  %_34 1000	[test7.c:16]
  %_35 true	[test7.c:16]
_bb4:
verifier.error:
verifier.error.split:
```

Here, there are two DSA nodes and two memory regions `%_0` and `%_1`.
Region `%_0` starts at address `0xbeef0`, and contains a value `42`
and a value `0xbeefc`. Region `%_1` starts at `0xbeefc` and contains
value `526`. Thus, regions `%_0` contains a pointer to region `%_1`,
as is expected based on the example.

# Contributors

Arie Gurfinkel
