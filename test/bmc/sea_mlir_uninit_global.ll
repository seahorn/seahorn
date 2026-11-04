; sea-mlir export: a global initializer the export cannot write is an error
; (export-only exits with status 1); --horn-sea-mlir-allow-uninit-globals
; makes it a warning.
; RUN: not %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=ERR
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-allow-uninit-globals --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=WARN
; ERR: Error: sea-mlir export: the initializer of global gp is dropped
; ERR: export failed
; WARN: Warning: sea-mlir export: the initializer of global gp is dropped
; WARN: sea-mlir-export: wrote
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"
@g = global i32 1, align 4
@gp = global ptr @g, align 8
declare i32 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
define i32 @main() {
entry:
  %p = load ptr, ptr @gp, align 8
  %v = load i32, ptr %p, align 4
  %c = icmp eq i32 %v, 1
  call void @verifier.assume.not(i1 %c)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
