; RUN: %seainspect "%s" --print-gsa --log=gsa  2>&1 | OutputCheck %s --comment=";" 

; ModuleID = '/tmp/test-gsa-1.bc'

; CHECK: GSA: Running on main
; Function Attrs: nounwind
define i32 @main(i1 %a, i1 %b, i1 %c, i1 %d) #0 {
bb0:
  %tmp1 = call i32 @nd()
  %tmp2 = call i32 @nd()
  %tmp3 = call i32 @nd()
  br i1 %a, label %bb1, label %bb5

bb1:
  br i1 %b, label %bb2, label %bb3

bb2:
  br label %bb4

bb3:
  br i1 %c, label %bb4, label %bb6

bb4:
  %val4 = phi i32 [%tmp1, %bb2], [%tmp2, %bb3]
; CHECK:      %val4 = phi i32
; CHECK-NEXT:	0: bb4 <- bb2	gate: i1 %b
; CHECK-NEXT:	gating condition: i1 %b
; CHECK-NEXT:	1: bb4 <- bb3	gate: i1 %c
; CHECK-NEXT:	gating condition: i1 %c

  br label %bb7

bb5:
  br label %bb6

bb6:
  %val6 = phi i32 [%tmp1, %bb3], [%tmp3, %bb5]
; CHECK:      %val6 = phi i32
; CHECK-NEXT: 0: bb6 <- bb3	gate: i1 %c
; CHECK-NEXT: gating condition:   %seahorn.gsa.br.neg.c = icmp eq i1 %c, false
; CHECK-NEXT: 1: bb6 <- bb5	gate: i1 %a
; CHECK-NEXT: gating condition:   %seahorn.gsa.br.neg.a = icmp eq i1 %a, false

  br label %bb7

bb7:
  %val7 = phi i32 [%val4, %bb4], [%val6, %bb6]
; CHECK:      %val7 = phi i32
; CHECK-NEXT: 0: bb7 <- bb4	gate: i1 %b
; CHECK-NEXT: gating condition: i1 %b
; CHECK-NEXT: 1: bb7 <- bb6	gate: i1 %a
; CHECK-NEXT: gating condition: i1 %a

  br i1 %d, label %bb8, label %bb9

bb8:
  %val8 = add i32 %val7, %tmp2
  br label %bb10

bb9:
  %val9 = add i32 %val7, %tmp3
  br label %bb10

bb10:
  %val10 = phi i32 [%val8, %bb8], [%val9, %bb9]
; CHECK:      %val10 = phi i32
; CHECK-NEXT: 0: bb10 <- bb8	gate: i1 %d
; CHECK-NEXT: gating condition: i1 %d
; CHECK-NEXT: 1: bb10 <- bb9	gate: i1 %d
; CHECK-NEXT: gating condition:   %seahorn.gsa.br.neg.d = icmp eq i1 %d, false

  %add10 = add i32 %val10, 42
  ret i32 %add10
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #1

declare i32 @nd() #2

; Function Attrs: noreturn
declare void @__VERIFIER_error() #3

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #1

attributes #0 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { noreturn }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 5.0.1-4 (tags/RELEASE_501/final)"}
