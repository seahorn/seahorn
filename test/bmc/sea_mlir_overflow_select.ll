; sea-mlir export: a select of two *.with.overflow results is a select of
; their values and a select of their overflow bits. The property holds
; (sea-vc --lower: unsat), as for the phi (sea_mlir_overflow_phi.ll).
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG-NOT: Error
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK: %[[C:v[0-9]+]] = sea.nondet "nd.i1"
; CHECK: %[[A:v[0-9]+]] = sea.add
; CHECK: %[[AO:v[0-9]+]] = sea.saddo
; CHECK: %[[B:v[0-9]+]] = sea.add
; CHECK: %[[BO:v[0-9]+]] = sea.saddo
; CHECK: %[[V:v[0-9]+]] = sea.select %[[C]], %[[A]], %[[B]] : i64
; CHECK: %[[O:v[0-9]+]] = sea.select %[[C]], %[[AO]], %[[BO]] : i1
; CHECK: sea.icmp eq, %[[V]], %{{v[0-9]+}} : i64
; CHECK: sea.icmp eq, %[[O]], %{{v[0-9]+}} : i1
; CHECK: sea.assert
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i64 @nd()
declare i1 @nd.i1()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

define i32 @main() {
entry:
  %x = call i64 @nd()
  %y = call i64 @nd()
  %c = call i1 @nd.i1()
  %ra = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %x, i64 %y)
  %rb = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %x, i64 1)
  %r = select i1 %c, { i64, i1 } %ra, { i64, i1 } %rb
  %v = extractvalue { i64, i1 } %r, 0
  %o = extractvalue { i64, i1 } %r, 1
  %yy = select i1 %c, i64 %y, i64 1
  %ev = add i64 %x, %yy
  %sx = icmp slt i64 %x, 0
  %sy = icmp slt i64 %yy, 0
  %sv = icmp slt i64 %ev, 0
  %same = icmp eq i1 %sx, %sy
  %flip = icmp ne i1 %sv, %sx
  %eo = and i1 %same, %flip
  %okv = icmp eq i64 %v, %ev
  %oko = icmp eq i1 %o, %eo
  %ok = and i1 %okv, %oko
  call void @verifier.assume.not(i1 %ok)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
