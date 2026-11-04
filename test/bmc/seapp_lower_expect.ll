; seapp: llvm.expect is kept by the default pipeline (dev18 behavior);
; --seapp-lower-expect lowers it to branch weights first. sea turns the
; option on for --horn-bmc-engine=sea-mlir.
; RUN: rm -f %t.old.ll %t.new.ll %t.mlir.ll
; RUN: %sea pp -S %s -o %t.old.ll
; RUN: filecheck %s --check-prefix=OLD < %t.old.ll
; RUN: %sea pp -S --seapp-lower-expect %s -o %t.new.ll
; RUN: filecheck %s --check-prefix=NEW < %t.new.ll
; RUN: %sea pp -S --horn-bmc-engine=sea-mlir %s -o %t.mlir.ll
; RUN: filecheck %s --check-prefix=NEW < %t.mlir.ll
; OLD: call i64 @llvm.expect.i64
; NEW-NOT: llvm.expect
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i32 @nd()
declare void @__VERIFIER_error()
declare i64 @llvm.expect.i64(i64, i64)

define i32 @main() {
entry:
  %x = call i32 @nd()
  %c = icmp eq i32 %x, 3
  %z = zext i1 %c to i64
  %e = call i64 @llvm.expect.i64(i64 %z, i64 0)
  %t = icmp ne i64 %e, 0
  br i1 %t, label %err, label %ok
err:
  call void @__VERIFIER_error()
  unreachable
ok:
  ret i32 0
}
