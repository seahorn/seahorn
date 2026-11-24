; RUN: %seabmc "%s" 2>&1 | %oc %s

; CHECK: {{^unsat$}}
;; llvm.u{add,sub}.sat at boundary values, and a symbolic property:
;; uadd.sat(x, y) >= x. (SeaHorn's BvOpSem2 leaves s{add,sub}.sat
;; unhandled: nondet results.)
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

declare i8 @llvm.uadd.sat.i8(i8, i8)
declare i8 @llvm.usub.sat.i8(i8, i8)
declare i8 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare void @verifier.error()

define i32 @main() {
entry:
  %a = call i8 @llvm.uadd.sat.i8(i8 250, i8 10)   ; 255
  %b = call i8 @llvm.usub.sat.i8(i8 5, i8 10)     ; 0
  %g = call i8 @llvm.uadd.sat.i8(i8 3, i8 4)      ; 7
  %x = call i8 @nd()
  %y = call i8 @nd()
  %s = call i8 @llvm.uadd.sat.i8(i8 %x, i8 %y)
  %ka = icmp eq i8 %a, -1
  %kb = icmp eq i8 %b, 0
  %kg = icmp eq i8 %g, 7
  %ks = icmp uge i8 %s, %x
  %r1 = and i1 %ka, %kb
  %r6 = and i1 %r1, %kg
  %r7 = and i1 %r6, %ks
  call void @verifier.assume.not(i1 %r7)
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
