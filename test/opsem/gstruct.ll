; RUN: %seabmc "%s" 2>&1 | %oc %s
; CHECK: ^unsat$
; ModuleID = '/tmp/sea-n9bqyN/gstruct.pp.ms.bc'
source_filename = "test-globals/gstruct.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@a = internal unnamed_addr global [3 x i32] [i32 1, i32 2, i32 3], align 4
@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*)], section "llvm.metadata"

declare i32 @unknown1(...) local_unnamed_addr #0

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
  %0 = tail call i32 bitcast (i32 (...)* @unknown1 to i32 ()*)() #3
  %1 = icmp eq i32 %0, 0
  br i1 %1, label %._crit_edge, label %.lr.ph

.lr.ph:                                           ; preds = %entry
  br label %2

; <label>:2:                                      ; preds = %.lr.ph, %2
  %.0.i1 = phi i32 [ 1, %.lr.ph ], [ %6, %2 ]
  %3 = load i32, i32* getelementptr inbounds ([3 x i32], [3 x i32]* @a, i32 0, i32 1), align 4, !tbaa !3
  %4 = icmp eq i32 %3, 2
  %5 = select i1 %4, i32 2, i32 1
  %6 = add nsw i32 %5, %.0.i1
  store i32 %6, i32* getelementptr inbounds ([3 x i32], [3 x i32]* @a, i32 0, i32 2), align 4, !tbaa !8
  store i32 %6, i32* getelementptr inbounds ([3 x i32], [3 x i32]* @a, i32 0, i32 0), align 4, !tbaa !9
  %7 = tail call i32 bitcast (i32 (...)* @unknown1 to i32 ()*)() #3
  %8 = icmp eq i32 %7, 0
  br i1 %8, label %._crit_edge.loopexit, label %2

._crit_edge.loopexit:                             ; preds = %2
  br label %._crit_edge

._crit_edge:                                      ; preds = %._crit_edge.loopexit, %entry
  %9 = load i32, i32* getelementptr inbounds ([3 x i32], [3 x i32]* @a, i32 0, i32 2), align 4, !tbaa !8
  %10 = icmp sgt i32 %9, 0
  br i1 %10, label %11, label %verifier.error

; <label>:11:                                     ; preds = %._crit_edge
  %12 = load i32, i32* getelementptr inbounds ([3 x i32], [3 x i32]* @a, i32 0, i32 0), align 4, !tbaa !9
  %13 = icmp sgt i32 %12, 0
  tail call void @verifier.assume.not(i1 %13) #3
  br label %verifier.error

verifier.error:                                   ; preds = %._crit_edge, %11
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
!2 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
!3 = !{!4, !5, i64 4}
!4 = !{!"X", !5, i64 0, !5, i64 4, !5, i64 8}
!5 = !{!"int", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
!8 = !{!4, !5, i64 8}
!9 = !{!4, !5, i64 0}
