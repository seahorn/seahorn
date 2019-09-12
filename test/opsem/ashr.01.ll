; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s
;; within the loop, use ashr to shift x by 1 and y by 2, assume y to be greater or equal to x
; CHECK: ^sat$
; ModuleID = 'ashr.01.ll'
source_filename = "ashr.01.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*)], section "llvm.metadata"

declare i32 @nd() local_unnamed_addr #0

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind
define i32 @main() local_unnamed_addr #2 {
entry:
  tail call void @seahorn.fn.enter() #3
  %0 = tail call i32 @nd() #3
  %1 = icmp eq i32 %0, 0
  br i1 %1, label %verifier.error, label %.lr.ph

.lr.ph:                                           ; preds = %entry
  br label %2

; <label>:2:                                      ; preds = %.lr.ph, %2
  %.01.i1 = phi i32 [ 1, %.lr.ph ], [ %3, %2 ]
  %3 = ashr i32 %.01.i1, 1
  %4 = tail call i32 @nd() #3
  %5 = icmp eq i32 %4, 0
  br i1 %5, label %.verifier.error_crit_edge, label %2

.verifier.error_crit_edge:                        ; preds = %2
  %.01.i1.lcssa = phi i32 [ %.01.i1, %2 ]
  %.lcssa = phi i32 [ %3, %2 ]
  %6 = ashr i32 %.01.i1.lcssa, 2
  br label %verifier.error

verifier.error:                                   ; preds = %.verifier.error_crit_edge, %entry
  %.01.i.lcssa = phi i32 [ %.lcssa, %.verifier.error_crit_edge ], [ 1, %entry ]
  %.0.i.lcssa = phi i32 [ %6, %.verifier.error_crit_edge ], [ 1, %entry ]
  %7 = icmp sge i32 %.01.i.lcssa, %.0.i.lcssa
  tail call void @verifier.assume(i1 %7) #3
  tail call void @seahorn.fail() #3
  ret i32 42
}

attributes #0 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 5.0.1-4 (tags/RELEASE_501/final)"}
