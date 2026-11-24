; LowerGvInitializers: a main-only global promoted to an alloca gets its
; type's ABI alignment by default (dev18 behavior); with
; --horn-lower-gv-init-keep-align it keeps the global's alignment. The
; sea-mlir engine turns the option on.
; RUN: rm -f %t.old.ll %t.new.ll %t.mlir.ll
; RUN: %horn --oll=%t.old.ll %s
; RUN: filecheck %s --check-prefix=OLD < %t.old.ll
; RUN: %horn --horn-lower-gv-init-keep-align --oll=%t.new.ll %s
; RUN: filecheck %s --check-prefix=NEW < %t.new.ll
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir --oll=%t.mlir.ll %s
; RUN: filecheck %s --check-prefix=NEW < %t.mlir.ll
; OLD: %g = alloca i32, align 4
; NEW: %g = alloca i32, align 16
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
