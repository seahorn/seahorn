# Exporting C programs to sea-mlir

SeaHorn's bounded pipeline (`sea bpf`) can hand the program it produces to
sea-mlir instead of SeaHorn's own BMC VC generator: `--horn-bmc-engine=sea-mlir`
runs `SeaMlirEnginePass` (lib/seahorn/SeaMlirExport.cc), which writes `main`
as a `sea.program`. The options for this are shipped as a profile,
`share/seahorn/profiles/sea-mlir-export.yaml`; use it instead of assembling
options by hand or reusing verify-c-common's `sea.yaml`.

## Recommended command line

```sh
clang-18 -c -emit-llvm -D__SEAHORN__ -fdeclspec -O1 -Xclang -disable-llvm-optzns \
  -fgnu89-inline -m64 -g -I<seahorn>/include [-DKEY=VAL ...] -o prog.bc prog.c
sea yama -y sea-mlir-export [-y my.yaml] --bound=8 \
  --horn-sea-mlir-out=prog.mlir prog.bc
sea-vc prog.mlir --lower --seam --widen-memory=4
```

- Compile with clang first: `sea yama` splits `-DK=1` into `-DK 1`, so
  defines cannot go through yama.
- The profile sets the sub-command (`bpf`) and
  `--horn-sea-mlir-export-only`: `sea` exits after the export with status 0
  if it succeeded and 1 otherwise (no sea-vc run, no `|| true` needed).
- Per run, on the command line or in the program's own yaml (given after the
  profile; later files and the command line override earlier ones): the
  unroll bound `--bound=N`, the output `--horn-sea-mlir-out=FILE`, and, to
  keep the intermediate bitcode, `--temp-dir=DIR --keep-temps` (a fresh DIR
  per run). Without them each run uses its own temporary directory.
- `--horn-sea-mlir-allow-uninit-globals` turns a global initializer the
  export cannot write into a warning (the global starts uninitialized, i.e.
  nondet) instead of an error. It is not in the profile: decide per program.
- `--horn-sea-mlir-allow-uninit-global=NAME` does the same for the global
  `NAME` only (its LLVM name, as the error prints it); repeat it or give a
  comma-separated list (`=a,b`). Prefer it to the flag above: a new dropped
  initializer elsewhere stays an error. A listed name that is not a global
  whose initializer is dropped (no such global, or its initializer is
  written) is a warning, a stale entry, not an error. The error for a
  dropped initializer names the option that allows it.

## What the profile contains

Only options that change the exported program: the pre-processing options
(`inline`, `devirt-functions`, `externalize-addr-taken-functions`,
`no-kill-vaarg`, `with-arith-overflow`, `ignore-define-verifier-fns`),
`-O3`, the shadow-memory analysis (`dsa: sea-cs-t`), `bmc: opsem` (BMC mode,
which also sets `--horn-shadow-mem-alloc-is-def`, which the export relies
on), `horn-unify-assumes: false`, and the engine selection.

`horn-unify-assumes` must be false: UnifyAssumes runs before the engine
(tools/seahorn/seahorn.cpp, new-PM route) and folds every assume of `main` into
one; that form is only for SeaHorn's gsa + dataflow + coi VC.

verify-c-common's options for SeaHorn's VC generator (`horn-gsa`,
`horn-vcgen-only-dataflow`, `horn-bmc-coi`, `horn-vcgen-use-ite`,
`horn-bv2-lambdas`, `horn-bv2-simplify`, `horn-bv2-extra-widemem`,
`sea-opsem-allocator`, `horn-explicit-sp0`) are read only by BmcPass, VCGen
and BvOpSem2, which do not run with the sea-mlir engine; the debug options
(`-S`, `keep-temps`, `temp-dir`, `horn-stats`) do not change the export.

## C++ extern templates

libstdc++ declares some class templates `extern template` (for example
`extern template class basic_string<char>`). clang then emits their inline
members as `available_externally` definitions: the body is a copy of a
definition in another module. seapp's InternalizePass keeps that linkage, and
`--horn-inline-all` inlines only internal functions, so the calls stay and
the export fails on them.

`--seapp-define-available-externally` gives these function definitions
`linkonce_odr` linkage before InternalizePass, which then makes them
internal, so they are inlined like other definitions. The body is the
ODR-equivalent definition of the function, so the program does not change.
`sea` turns the option on for `--horn-bmc-engine=sea-mlir` (so with the
profile) unless it is given explicitly; SeaHorn's own engines are
unchanged. `--seapp-define-available-externally=false` turns it off.
`--seapp-stats` prints the number of functions changed
(`pp.avail-ext.defined`); `--log=avail-ext` names them.

- Global variables are not changed. An `available_externally` global keeps
  its linkage and its initializer, as in SeaHorn's own pipeline.
- Members that are not inline (in libstdc++'s `basic_string`, `_M_create`,
  `_M_mutate`, `_M_replace`, among others) are only declared under an extern
  template, so they remain external calls. Model them, or compile with
  `-D_GLIBCXX_ASSERTIONS`, which turns off the `basic_string` extern
  templates (and enables libstdc++'s precondition checks).

## Export errors

An instruction the export does not support is an error that names the
instruction and the reason. The export goes on, so one run shows every
unsupported construct, but the values computed from a failed instruction
have no definition:

- At the first use of such a value, one error names the instruction that
  failed and its reason (``operand %v is undefined because `<instruction>`
  failed to export (<reason>)``). Further uses of values derived from the same
  cause are not reported; a warning at the end counts them.
- A call to a function the module defines means that the call was not
  inlined. It is reported once per callee, naming one call site; a warning
  counts the other call sites. The shadow memory gives such a call
  `shadow.mem.arg.mod` / `shadow.mem.arg.new` versions, which the export
  usually meets first; they are reported as the call that was not inlined.
  A common cause is recursion (`std::sort`'s `__introsort_loop`).
  `available_externally` definitions are inlined since
  `--seapp-define-available-externally` (see below).

## Trusted annotations: TBAA

The shadow-memory optimizer (sea-dsa, `--horn-shadow-mem-optimize`) gives
each load the latest memory version that may write the loaded bytes. With
`--horn-shadow-mem-use-tbaa` (the default) it trusts the front end's
type-based alias metadata: a store through one type does not clobber a load
through an unrelated type, so the load can read a version from before that
store. This is sound for programs that follow C/C++ strict aliasing, and it
gives alias facts that the pointer analysis alone does not.

A program that breaks strict aliasing gets stale values. The typical case is
a mock of a library type written through a mirror struct of the same layout:
the mock's stores carry the mirror's TBAA tag, the library's loads carry the
library type's tag, and the loads skip the mock's stores. A reach can then be
unsat although the program reaches it (a vacuous proof).

When TBAA decides that a load skips a store, the export says so:

```
Warning: sea-mlir export: TBAA moved N shadow-memory uses past stores; to check whether a result depends on it, re-export with --horn-shadow-mem-use-tbaa=false
```

and the exported program has the same text as a comment after its first
line. N counts the loads whose memory version differs from the one they get
without TBAA (a skip that BasicAA, ScopedNoAliasAA or the allocation-site
check would also make is not counted). N is summed over the module; the
export translates `main` only, so after inlining these are `main`'s loads.
`--log=shadow-mem-tbaa` prints each such load and the first store TBAA
skipped for it, with their source positions. SeaHorn's own engines report
the same numbers as statistics (`--horn-stats`):
`shadow.mem.tbaa-moved-uses` (N) and `shadow.mem.tbaa-noalias-skips` (the
(load, store) pairs in which the load skipped the store because of TBAA
alone; one load can skip several stores).

A warning is not an error: in a well-typed program every such skip is
correct (a load of a `long` that skips a store of a pointer, when the
pointer analysis cannot separate the two). `--horn-shadow-mem-use-tbaa=false` is a diagnosis aid: if a suspicious
unsat (or a vacuity check that fails) changes with it, the result depends on
TBAA. It is not a setting to keep, since it gives up the alias facts above.
The fix is in the program: mock only what the proof needs, and when a
library type must be mocked, write the mock against the real type (its own
API, or explicit specializations) so its accesses carry the library's TBAA
tags, never through a mirror struct.

sea-mlir's interpreter gives an independent hint: `sea-run` on the exported
program warns `interp.load-earlier-version` at each load whose memory
operand is not the latest version of its memory on the executed path. Every
skip the optimizer makes triggers it, also the correct ones, so it points at
the loads to inspect rather than proving a stale read. At such a load
`sea-run` reads the current contents, so if `sea-run` reaches an assertion
on inputs that `sea-vc` says cannot reach it, one of the flagged loads reads
a stale version.

## Heap allocation

- `malloc(n)` is `sea.malloc n align 16`; `calloc(n, k)` is `sea.malloc`
  of `n*k` bytes followed by a `sea.memset` to zero; `free(p)` is
  `sea.free p`.
- C++ `operator new` and `operator new[]` (`_Znwm`, `_Znam`, and their
  `std::nothrow_t` and `std::align_val_t` forms) are `sea.malloc` of their
  size argument. A constant `std::align_val_t` that is a power of two is the
  object's alignment; any other is a warning and the alignment is 16, as for
  `malloc`.
- C++ `operator delete` and `operator delete[]` (`_ZdlPv`, `_ZdaPv`, their
  sized, `std::align_val_t` and `std::nothrow_t` forms) are `sea.free` of
  their pointer argument. `delete` of null, like `free(NULL)`, does nothing.
  Mixing `new[]` with `delete` (or `malloc` with `delete`) is not detected.
- `sea.malloc` always succeeds, so `malloc` and `calloc` never return null,
  and neither do the `std::nothrow_t` forms of `operator new`. A program
  whose correctness depends on handling allocation failure is not checked
  on that path.
- These names are recognized also when the module defines them (a
  replacement `operator new`); a call that was not inlined is the
  allocation, not the replacement's body.

## Arithmetic with overflow

`llvm.{s,u}{add,sub,mul}.with.overflow` (from `__builtin_*_overflow`, UBSan's
`-fsanitize=signed-integer-overflow`, `--with-arith-overflow`) has no sea
op of its own: its value field is the plain op (`sea.mul`) and its overflow
bit an overflow op (`sea.smulo`), and each `extractvalue` of the result picks
one of them. The result is never a sea struct: it stays two values, and so
do the instructions that carry it, field by field:

- a `phi` of results (unrolling and GVN merge them) is two block arguments;
- a `select` of results is two `sea.select`s;
- a `freeze` of a result (InstCombine and SimplifyCFG add one) has the same
  two fields;
- an `insertvalue` into a result replaces one field.

The other operand of such a phi or select may be an `{iN, i1}` constant
(its fields; an undef or poison field is a nondet value) or any other
`{iN, i1}` value (its `sea.struct.extract` fields). Any other use of a
result, for example as an operand of an `insertvalue` into a larger struct
or of a call, is an error that names the use.

## Counterexample prints: sea_printf

`sea_printf(const char *fmt, ...)` (declare it as
`extern __declspec(noalias) void sea_printf(const char *format, ...);`, as
verify-c-common's `utils.h` does, or include `seahorn/seahorn.h`) is
exported as sea-mlir print ops (sea-mlir `docs/design/Print.md`). Prints encode nothing in the VC; `sea-vc` shows them
when it replays a sat model (`print:` lines after `replay:`):

```c
sea_printf("x=%d u=%u p=%p\n", x, u, p);
sea_printf("pre: tx_wnd=%u inc=%d\n", w, i);
```
```
print: x = -3 : si32
print: u = 7 : ui32
print: p = &stack.4[2]
print: pre.tx_wnd = 1502 : ui32
print: pre.inc = 9 : si32
```

- Each integer or pointer argument becomes one strong `sea.print` (an SSA
  use: kept alive through sea-mlir's passes). Its label is the trailing
  identifier-like token (`[A-Za-z_][A-Za-z0-9_.\[\]]*`) of the format's text
  before the conversion, after the `=`, `:`, `,`, `;`, `(` and spaces that
  end it (`"x=%d"` and `" inc=%d"` give `x` and `inc`, `"s.a[0] = %d"` gives
  `s.a[0]`); else the variable an `llvm.dbg.value` says the argument holds
  (with `-g`); else the argument's LLVM name, unless SeaHorn generated it
  (`_N`, see Locations); else `arg<k>`.
- The format's leading text before its first label is a print scope around
  the call's prints (`sea.print.scope "<tag>"` ... `sea.print.end "<tag>"`;
  sea-mlir shows the dotted path `pre.tx_wnd`). The tag is the text's words
  (letters, digits, `_`) from the first that starts with a letter or `_`,
  joined by `_`: `"pre: "` gives `pre`, `"after step 2: "` gives
  `after_step_2`; text without an identifier (`"--> "`) gives no scope. Text
  between conversions contributes only its trailing identifier. There is no
  scope when the format does not match the arguments.
- The conversion picks the format: `%d` `%i` signed, `%u` unsigned, `%x`
  `%X` hex, `%c` a character; others (and any integer when the format is not
  a constant string or its conversions do not match the arguments: a
  warning) print with sea-mlir's `auto`. Pointers always print as an object
  and an offset.
- A string literal argument (`%s` of a constant) prints as a tag line
  `label = "text"`; a call without arguments is a tag line with the format.
- A floating-point, aggregate or vector argument is not printed (a warning
  per argument).

The minimal format parser skips flags, width, precision and length
modifiers; `*` and `%n` make it give up (positional labels, `auto`).

## Counterexample prints: sea_memdump

`sea_memdump(const char *label, const void *p, size_t n)` (declared, with
`sea_printf`, in `seahorn/seahorn.h`) prints the `n` bytes at `p` as a hex
dump in a sea-mlir counterexample:

```c
sea_memdump("buf", buf, sizeof buf);
```
```
print: buf = stack.4[0..8]
print: buf +00: 60 41 41 51 41 41 41 41                         |`AAQAAAA|
```

- It is exported as a strong `sea.print.mem "<label>" %m[%p], %n :
  !sea.mem<...>, iN -> i8 {fmt = "hexdump"}` in the memory version current
  at the call. The count may be symbolic; sea-mlir caps it at 65536.
- The memory version comes from the shadow memory: with
  `--horn-bmc-engine=sea-mlir`, `SeaMlirPrepPass` (before the shadow memory)
  gives `sea_memdump` a body that reads `*p`, so each call gets a
  `shadow.mem.arg.ref` (a use of `p`'s region, no new version). The body is
  never exported.
- The label is the string literal; any other label prints as `sea_memdump`
  (a warning). A pointer without a shadow-memory region is not printed (a
  warning).
- Every other flow (SeaHorn's BMC, CHC, crab) leaves it an external call
  that is passed `p` (PromoteVerifierCalls removes a body a program gives
  it): verdicts do not change, but the compiler keeps the dumped memory
  alive (test/bmc/sea_memdump_verdict.c).

## Locations

An op's location is the C location of the LLVM instruction it comes from
(with `-g`), in MLIR's location syntax:

- `"path":line:col`: the path is the DIFile's directory and name, relative
  to the compilation directory of the module's (first) compile unit when it
  lies under it, else absolute (`"src/h2fc_step.c":139:24`,
  `"/opt/fd/src/util/bits/fd_bits.h":421:1`).
- An instruction inlined from a callee: `callsite(<callee position> at
  <call position>)`, nested along the DILocation's inlinedAt chain, the
  innermost position first: `callsite("fd_h2_conn.c":564:7 at
  callsite("fd_h2_conn.c":375:9 at "h2fc_step.c":255:3))`. sea-vc shows the
  innermost position (`assert-at`, `at=`).
- A source name: `"x"(<position>)` (a NameLoc), when the instruction has a
  name SeaHorn did not generate. Generated names are left out, so they do not
  show as `at_name=` in counterexamples: NameValues' `_N` (also `_N.lcssa`
  and other suffixes LLVM derives from it) and the shadow memory's `sm<N>`
  versions, their phis and `shadow.mem.<N>` slots.
- A constant materialized for an instruction (`sea.const`, `sea.ptr.null`,
  ...) gets the instruction's position, not its name. A global
  (`sea.global`) gets its DIGlobalVariable's file and line, column 0 (the
  object table's `at=`).
- An op without a debug location has none in the file; the MLIR parser
  gives it its position in the `.mlir`.

Locations do not change the VC: `sea-vc --smt2` gives the same query.

### Debugging mode: the LLVM level

For the rare case where the C program and the MLIR do not match (a new
front end, a compiler or modelling issue), `--horn-sea-mlir-ll-out=FILE`
(not in the profile) writes the LLVM module the export translated, after all
of SeaHorn's passes, to FILE as `.ll`, and links every op's location to its
instruction there:

```
%v128 = sea.nondet "nd_int" [2] : i32 loc(fused<"llvm @main %entry #5">["l.c":15:11])
sea.assert %v138 loc(fused<"llvm @main %entry.split #1">["prog.mlir":150:3])
%v65 = sea.global @"tab" ... loc(fused<"llvm @tab">["l.c":6:0])
```

- The FusedLoc's metadata is `llvm @<function> %<block> #<i>`: the block as
  the `.ll` names it (its label, or its slot number when it has no name),
  and `i` the instruction's 0-based ordinal in the block (count the lines
  after the label). A global's link is `llvm @<global>`. All ops exported
  from one instruction share its link.
- To follow an op: C position (its file location) -> `.ll` instruction (the
  link) -> MLIR op (the op itself). The `.ll` keeps SeaHorn's generated
  names (`%_N`, `%sm<N>`), which the MLIR locations do not show.
- An op without a source position gets its position in the `.mlir` (the
  MLIR parser does not give one to an op that has a location): sea-vc's
  `assert-op` and `at=` show the same as without the option. A source name
  stays the outer NameLoc (`"x"(fused<...>[...])`), so VC symbol names and
  the query do not change.
## Profiles by name

`sea yama -y NAME` with a NAME that is not an existing file, has no `/` and
is not a URL is looked up as `NAME.yaml` in the directories of
`$SEAHORN_PROFILE_PATH` (colon-separated), then in
`<prefix>/share/seahorn/profiles` (`<prefix>` = the parent of the directory
of the `sea` script); yama prints the file it used. Shipped profiles:

| name | use |
|------|-----|
| `sea-mlir-export` | export to sea-mlir (this page) |
| `vcc` | verify-c-common's configuration for SeaHorn's own BMC (`sea yama -y vcc bpf ...`) |
| `vcc-cex` | verify-c-common's counterexample configuration (instead of `vcc`) |
| `vcc-vac` | verify-c-common's vacuity overlay (`-y vcc -y vcc-vac`) |
| `vcc-pcond` | verify-c-common's path-condition overlay (`-y vcc -y vcc-pcond`) |

The `vcc*` profiles are copies of verify-c-common's `seahorn/*.yaml` (see
each file's header); they are the usual starting point for a SeaHorn
configuration of your own, but not for a sea-mlir export.
