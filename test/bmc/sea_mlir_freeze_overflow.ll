; sea-mlir export: InstCombine / SimplifyCFG may freeze the {iN, i1} result
; of a *.with.overflow intrinsic before its extractvalues; the frozen value
; has the same fields (the value and the overflow bit are never poison).
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG-NOT: Error
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK: %[[M:v[0-9]+]] = sea.mul %[[X:v[0-9]+]], %[[Y:v[0-9]+]] : i64
; CHECK: %[[O:v[0-9]+]] = sea.smulo %[[X]], %[[Y]] : i64
; CHECK: sea.icmp ult, %[[M]], %{{v[0-9]+}} : i64
; CHECK: sea.select %[[O]],
; CHECK: sea.assert
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i64 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare { i64, i1 } @llvm.smul.with.overflow.i64(i64, i64)

define i32 @main() {
entry:
  %x = call i64 @nd()
  %y = call i64 @nd()
  %r = call { i64, i1 } @llvm.smul.with.overflow.i64(i64 %x, i64 %y)
  %r.fr = freeze { i64, i1 } %r
  %r.fr2 = freeze { i64, i1 } %r.fr
  %m = extractvalue { i64, i1 } %r.fr, 0
  %o = extractvalue { i64, i1 } %r.fr2, 1
  %lt = icmp ult i64 %m, 100
  %ok = select i1 %o, i1 true, i1 %lt
  call void @verifier.assume.not(i1 %ok)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
