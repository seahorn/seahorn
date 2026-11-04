; sea-mlir engine: when main cannot reach seahorn.fail after the pipeline
; (the front end decided every assertion), the export is a program whose
; only assertion is true (unsat for sea-vc), not an error.
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG: main cannot reach seahorn.fail
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK-NEXT: %[[T:v[0-9]+]] = sea.const 1 : i1
; CHECK-NEXT: sea.assert %[[T]]
; CHECK-NEXT: sea.halt
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"
@g = internal global i32 3, align 16
declare i32 @nd()
define i32 @main() {
  %x = call i32 @nd()
  store i32 %x, ptr @g, align 16
  %v = load i32, ptr @g, align 16
  ret i32 %v
}
