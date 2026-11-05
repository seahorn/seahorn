; sea-mlir export: --horn-sea-mlir-allow-uninit-global=NAME allows a dropped
; initializer for the named globals only; another dropped initializer stays
; an error. --horn-sea-mlir-allow-uninit-globals still allows every one. A
; listed name that is not a global with a dropped initializer is a warning.
; RUN: not %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=NONE
; RUN: not %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-allow-uninit-global=gp --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=ONE
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-allow-uninit-global=gp --horn-sea-mlir-allow-uninit-global=gq --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=BOTH
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-allow-uninit-global=gq,gp --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=BOTH
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-allow-uninit-globals --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=ALL
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-allow-uninit-global=gp,gq,g,nosuch --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=STALE
; NONE-DAG: Error: sea-mlir export: the initializer of global gp is dropped {{.*}} (--horn-sea-mlir-allow-uninit-global=gp allows it)
; NONE-DAG: Error: sea-mlir export: the initializer of global gq is dropped {{.*}} (--horn-sea-mlir-allow-uninit-global=gq allows it)
; NONE: export failed
; ONE-NOT: Error: {{.*}} global gp
; ONE-DAG: Warning: sea-mlir export: the initializer of global gp is dropped
; ONE-DAG: Error: sea-mlir export: the initializer of global gq is dropped
; ONE-NOT: Error: {{.*}} global gp
; ONE: export failed
; BOTH-NOT: Error
; BOTH-NOT: stale
; BOTH-DAG: Warning: sea-mlir export: the initializer of global gp is dropped
; BOTH-DAG: Warning: sea-mlir export: the initializer of global gq is dropped
; BOTH-NOT: Error
; BOTH-NOT: stale
; BOTH: sea-mlir-export: wrote
; ALL-NOT: Error
; ALL-DAG: Warning: sea-mlir export: the initializer of global gp is dropped
; ALL-DAG: Warning: sea-mlir export: the initializer of global gq is dropped
; ALL-NOT: Error
; ALL: sea-mlir-export: wrote
; STALE-NOT: Error
; STALE-DAG: Warning: sea-mlir export: --horn-sea-mlir-allow-uninit-global=g is stale: the initializer of this global is not dropped
; STALE-DAG: Warning: sea-mlir export: --horn-sea-mlir-allow-uninit-global=nosuch is stale: there is no such global
; STALE-NOT: Error
; STALE: sea-mlir-export: wrote
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"
@g = global i32 1, align 4
@gp = global ptr @g, align 8
@gq = global ptr @g, align 8
declare i32 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
define i32 @main() {
entry:
  %p = load ptr, ptr @gp, align 8
  %v = load i32, ptr %p, align 4
  %q = load ptr, ptr @gq, align 8
  %w = load i32, ptr %q, align 4
  %s = add i32 %v, %w
  %c = icmp eq i32 %s, 2
  call void @verifier.assume.not(i1 %c)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
