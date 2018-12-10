; RUN: %seainspect "%s" --print-gsa --log=gsa  2>&1 | OutputCheck %s --comment=";" 

; ModuleID = '/tmp/test-gsa-1.bc'

; CHECK: GSA: Running on main
; Function Attrs: nounwind
define i32 @main() #0 {
bb:
  %tmp = call i32 @nd()
  switch i32 %tmp, label %bb7 [ i32 0, label %bb1
                                i32 2, label %bb2
                                i32 3, label %bb1
                                i32 5, label %bb3
                                i32 7, label %bb4
                                i32 8, label %sink ]

bb1:
  br label %sink

bb2:
  br label %sink

bb3:
  br label %sink

bb4:
  %tmp1 = call i32 @nd()
  %cond = icmp eq i32 %tmp1, 42
  br i1 %cond, label %bb5, label %bb6

bb5:
  br label %sink

bb6:
  br label %sink

bb7:
  br label %sink

sink:
  %val = phi i32 [1, %bb1 ], [2, %bb2], [3, %bb3], [5, %bb5], [6, %bb6], [7, %bb7], [8, %bb]
  ; CHECK:  %val = phi i32
  ; CHECK-NEXT: 0: sink
  ; CHECK-NEXT: gating condition:   %seahorn.gsa.cond.or = or i1 %seahorn.gsa.cmp, %seahorn.gsa.cmp2
  ; CHECK-NEXT: 1: sink
  ; CHECK-NEXT: gating condition:   %seahorn.gsa.cmp1 = icmp eq i32 %tmp, 2
  ; CHECK-NEXT: 2: sink
  ; CHECK-NEXT: gating condition:   %seahorn.gsa.cmp3 = icmp eq i32 %tmp, 5
  ; CHECK-NEXT: 3: sink
  ; CHECK-NEXT: gating condition:   %cond = icmp eq i32 %tmp1, 42
  ; CHECK-NEXT: 4: sink
  ; CHECK-NEXT: gating condition:   %seahorn.gsa.br.neg.cond = icmp eq i1 %cond, false
  ; CHECK-NEXT: 5: sink
  ; CHECK-NEXT: gating condition:   %seahorn.gsa.default.cond = icmp eq i1 %seahorn.gsa.default.or10, false
  ; CHECK-NEXT: 6: sink
  ; CHECK-NEXT: gating condition:   %seahorn.gsa.cmp5 = icmp eq i32 %tmp, 8

  br label %bb21

bb21:
  ret i32 %val
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
