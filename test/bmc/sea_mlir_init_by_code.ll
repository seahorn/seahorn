; SPDX-FileCopyrightText: 2026 The SeaHorn Authors
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception
; sea-mlir export: a global without a shadow.mem.global.init (a unique
; scalar) is initialized by code when main's entry block stores its whole
; value before anything may read memory; its initializer is then never read
; and is not reported as dropped, whatever the stored value (gp, gi). A
; store after a load (gl) does not count, nor does a store narrower than the
; global (gn, made before any read): those initializers are dropped. --lower-gv-init=false: the stores
; are the program's own.
; RUN: not %horn --lower-gv-init=false --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=ERR
; RUN: %horn --lower-gv-init=false --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-allow-uninit-global=gl,gn --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=ALLOW
; ERR-NOT: global gp
; ERR-NOT: global gi
; ERR-DAG: Error: sea-mlir export: the initializer of global gl is dropped
; ERR-DAG: Error: sea-mlir export: the initializer of global gn is dropped
; ERR-NOT: global gp
; ERR-NOT: global gi
; ERR: export failed
; ALLOW-NOT: Error
; ALLOW-NOT: global gp
; ALLOW-NOT: global gi
; ALLOW-NOT: stale
; ALLOW: sea-mlir-export: wrote
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"
@g = global i32 1, align 4
@gp = internal global ptr null, align 8
@gi = internal global i32 7, align 4
@gl = internal global ptr null, align 8
@gn = internal global i64 5, align 8
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
define i32 @main() {
entry:
  store ptr @g, ptr @gp, align 8
  store i32 7, ptr @gi, align 4
  store i32 0, ptr @gn, align 8
  %x = load i32, ptr @g, align 4
  store ptr null, ptr @gl, align 8
  %p = load ptr, ptr @gp, align 8
  %v = load i32, ptr %p, align 4
  %i = load i32, ptr @gi, align 4
  %l = load ptr, ptr @gl, align 8
  %n = load i64, ptr @gn, align 8
  %nt = trunc i64 %n to i32
  %lz = icmp eq ptr %l, null
  %lv = zext i1 %lz to i32
  %s0 = add i32 %v, %i
  %s1 = add i32 %s0, %x
  %s2 = add i32 %s1, %nt
  %s3 = add i32 %s2, %lv
  %c = icmp eq i32 %s3, 10
  call void @verifier.assume.not(i1 %c)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
