; RUN: %seainspect "%s" --print-gsa --log=gsa  2>&1 | OutputCheck %s --comment=";" 

; ModuleID = '/tmp/test-gsa-1.bc'

; CHECK: GSA: Running on main
; Function Attrs: nounwind
define i32 @main() #0 {
bb:
  %tmp = call i32 @nd()
  %tmp2 = icmp ne i32 %tmp, 0
  br i1 %tmp2, label %bb3, label %bb18

bb3:                                              ; preds = %bb
  %tmp4 = add nsw i32 1, 1
  %tmp5 = add nsw i32 1, 1
  %tmp6 = call i32 @nd()
  %tmp7 = icmp ne i32 %tmp6, 0
  br i1 %tmp7, label %bb8, label %bb11

bb8:                                              ; preds = %bb3
  %tmp9 = add nsw i32 %tmp4, 1
  %tmp10 = add nsw i32 %tmp5, 1
  br label %bb11

bb11:                                             ; preds = %bb8, %bb3
  %.01 = phi i32 [ %tmp9, %bb8 ], [ %tmp4, %bb3 ]
; CHECK:  %.01 = phi i32
; CHECK: gating condition:   %tmp7 = icmp ne i32 %tmp6, 0
; CHECK: gating condition:   %seahorn.gsa.br.neg.tmp7 = icmp eq i1 %tmp7, false

  %.0 = phi i32 [ %tmp10, %bb8 ], [ %tmp5, %bb3 ]
; CHECK: %.0 = phi i32
; CHECK: gating condition:   %tmp7 = icmp ne i32 %tmp6, 0
; CHECK: gating condition:   %seahorn.gsa.br.neg.tmp7 = icmp eq i1 %tmp7, false

  %tmp12 = call i32 @nd()
  %tmp13 = icmp ne i32 %tmp12, 0
  br i1 %tmp13, label %bb14, label %bb17

bb14:                                             ; preds = %bb11
  %tmp15 = add nsw i32 %.01, 1
  %tmp16 = add nsw i32 %.0, 1
  br label %bb17

bb17:                                             ; preds = %bb14, %bb11
  %.1 = phi i32 [ %tmp15, %bb14 ], [ %.01, %bb11 ]
; CHECK: %.1 = phi i32
; CHECK: gating condition:   %tmp13 = icmp ne i32 %tmp12, 0
; CHECK: gating condition:   %seahorn.gsa.br.neg.tmp13 = icmp eq i1 %tmp13, false

  br label %bb18

bb18:                                             ; preds = %bb17, %bb
  %.2 = phi i32 [ %.1, %bb17 ], [ 1, %bb ]
; CHECK: %.2 = phi i32 
; CHECK: gating condition:   %tmp2 = icmp ne i32 %tmp, 0
; CHECK: gating condition:   %seahorn.gsa.br.neg.tmp2 = icmp eq i1 %tmp2, false

  %tmp19 = icmp sle i32 %.2, 4
  br i1 %tmp19, label %bb21, label %bb20

bb20:                                             ; preds = %bb18
  call void @__VERIFIER_error() #4
  unreachable

bb21:                                             ; preds = %bb18
  ret i32 0
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
