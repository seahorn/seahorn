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
one of them. A `freeze` of the result (InstCombine and SimplifyCFG add one)
has the same two fields. Any other use of the `{iN, i1}` result is not
supported.

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
