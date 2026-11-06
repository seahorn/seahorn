; sea-mlir export: a phi of two *.with.overflow results is two block
; arguments, the value and the overflow bit; each predecessor passes the
; fields of its result. The property holds (sea-vc --lower: unsat): the
; fields equal an independent computation of x + y (or x + 1) and of its
; signed overflow.
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG-NOT: Error
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK: %[[A:v[0-9]+]] = sea.add %[[X:v[0-9]+]], %{{v[0-9]+}} : i64
; CHECK: %[[AO:v[0-9]+]] = sea.saddo %[[X]], %{{v[0-9]+}} : i64
; CHECK: sea.br ^bb3(%[[A]], %[[AO]] : i64, i1)
; CHECK: %[[B:v[0-9]+]] = sea.add %[[X]], %[[Y:v[0-9]+]] : i64
; CHECK: %[[BO:v[0-9]+]] = sea.saddo %[[X]], %[[Y]] : i64
; CHECK: sea.br ^bb3(%[[B]], %[[BO]] : i64, i1)
; CHECK: ^bb3(%[[V:v[0-9]+]] : i64, %[[O:v[0-9]+]] : i1):
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
  br i1 %c, label %a, label %b
a:
  %ra = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %x, i64 %y)
  br label %j
b:
  %rb = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %x, i64 1)
  br label %j
j:
  %r = phi { i64, i1 } [ %ra, %a ], [ %rb, %b ]
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
