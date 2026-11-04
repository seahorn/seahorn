; UfoOpSem: x | y = 0 says nothing about x and y by default (dev18
; behavior: sat); --horn-ufo-minmax-abs-or adds x | y = 0 => x = 0 && y = 0.
; RUN: %sea horn --solve %s 2>&1 | filecheck %s --check-prefix=OLD
; RUN: %sea horn --solve --horn-ufo-minmax-abs-or %s 2>&1 | filecheck %s --check-prefix=NEW
; OLD: {{^sat$}}
; NEW: {{^unsat$}}
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"
declare i32 @nd()
declare void @verifier.error()
define i32 @main() {
entry:
  %a = call i32 @nd()
  %b = call i32 @nd()
  %o = or i32 %a, %b
  %z = icmp eq i32 %o, 0
  %na = icmp ne i32 %a, 0
  %c = and i1 %z, %na
  br i1 %c, label %err, label %ok
err:
  call void @verifier.error()
  unreachable
ok:
  ret i32 0
}
