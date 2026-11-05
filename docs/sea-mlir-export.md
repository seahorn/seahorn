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

## Counterexample prints: sea_printf

`sea_printf(const char *fmt, ...)` (declare it as
`extern __declspec(noalias) void sea_printf(const char *format, ...);`, as
verify-c-common's `utils.h` does) is exported as sea-mlir print ops (sea-mlir
`docs/design/Print.md`). Prints encode nothing in the VC; `sea-vc` shows them
when it replays a sat model (`print:` lines after `replay:`):

```c
sea_printf("x=%d u=%u p=%p\n", x, u, p);
```
```
print: x = -3 : si32
print: u = 7 : ui32
print: p = &stack.4[2]
```

- Each integer or pointer argument becomes one strong `sea.print` (an SSA
  use: kept alive through sea-mlir's passes). Its label is the format's text
  before the conversion, without spaces and `=`, `:`, `,` (`"x=%d"` gives
  `x`); else the variable an `llvm.dbg.value` says the argument holds (with
  `-g`); else the argument's LLVM name, unless SeaHorn generated it
  (`_N`, see Locations); else `arg<k>`.
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

## Locations

Each op's location is the LLVM instruction's debug location (`file:line:col`,
with `-g`), inside a NameLoc with the instruction's name when that name is a
source name. Names SeaHorn generates are left out, so they do not show as
`at_name=` in sea-mlir's counterexamples: NameValues' `_N` (also `_N.lcssa`
and other suffixes LLVM derives from it) and the shadow memory's `sm<N>`
versions, their phis and `shadow.mem.<N>` slots. A constant materialized for
an instruction (`sea.const`, `sea.global`, ...) gets only its file location,
not the instruction's name. Locations do not change the VC: `sea-vc --smt2`
gives the same query.

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
