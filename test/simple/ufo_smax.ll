; UfoOpSem: llvm.smax is encoded by default (dev18 behavior: unsat);
; --horn-ufo-minmax-abs-or=false leaves it unconstrained (sat).
; RUN: %sea horn --solve --horn-ufo-minmax-abs-or=false %s 2>&1 | filecheck %s --check-prefix=OLD
; RUN: %sea horn --solve %s 2>&1 | filecheck %s --check-prefix=NEW
; OLD: {{^sat$}}
; NEW: {{^unsat$}}
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"
declare i32 @nd()
declare i32 @llvm.smax.i32(i32, i32)
declare void @verifier.error()
define i32 @main() {
entry:
  %a = call i32 @nd()
  %b = call i32 @nd()
  %m = call i32 @llvm.smax.i32(i32 %a, i32 %b)
  %c = icmp slt i32 %m, %b
  br i1 %c, label %err, label %ok
err:
  call void @verifier.error()
  unreachable
ok:
  ret i32 0
}
