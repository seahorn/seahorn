; SPDX-FileCopyrightText: 2026 The SeaHorn Authors
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; sea-mlir export: llvm.abs is sea.abs; is_int_min_poison = true becomes
; its nsw promise (sea-wrap-flags assumes or asserts it), false none.
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG-NOT: unsupported
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK: %[[X:v[0-9]+]] = sea.nondet {{.*}} : i64
; CHECK: sea.abs %[[X]] nsw : i64 loc("a64")
; CHECK: %[[Y:v[0-9]+]] = sea.trunc %[[X]] : i64 to i32
; CHECK-NOT: nsw
; CHECK: sea.abs %[[Y]] : i32 loc("a32")
; CHECK: sea.assert
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i64 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare i64 @llvm.abs.i64(i64, i1)
declare i32 @llvm.abs.i32(i32, i1)

define i32 @main() {
entry:
  %x = call i64 @nd()
  %a64 = call i64 @llvm.abs.i64(i64 %x, i1 true)
  %y = trunc i64 %x to i32
  %a32 = call i32 @llvm.abs.i32(i32 %y, i1 false)
  %w = sext i32 %a32 to i64
  %s = add i64 %a64, %w
  %neg = icmp slt i64 %s, -10
  call void @verifier.assume.not(i1 %neg)
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
