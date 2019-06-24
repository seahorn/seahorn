;; From issue #204 on github
; RUN: %seabmc "%s" 2>&1 | %oc %s
; CHECK: ^unsat$
;; ModuleID = '/var/folders/_j/1_4mrwbs7y16zbvj79vwvhdc0000gn/T/sea-zUjkuf/sea204.pp.ms.o.ul.cut.o.bc'
source_filename = "/tmp/sea204.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*) ], section "llvm.metadata"

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #0

declare i32 @nd() local_unnamed_addr #1

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #2

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #3 {
entry:
  %_1 = alloca [4 x i32], align 4
  tail call void @seahorn.fn.enter() #4
  %_2 = tail call i32 @nd() #4
  %_3 = bitcast [4 x i32]* %_1 to i8*
  call void @llvm.lifetime.start.p0i8(i64 16, i8* nonnull %_3) #4
  %_4 = icmp eq i32 %_2, 1
  call void @llvm.memset.p0i8.i64(i8* nonnull %_3, i8 0, i64 16, i32 4, i1 false)
  tail call void @verifier.assume(i1 %_4) #4
  %_5 = getelementptr inbounds [4 x i32], [4 x i32]* %_1, i32 0, i32 %_2
  %_6 = load i32, i32* %_5, align 4, !tbaa !4
  %_7 = icmp eq i32 %_6, 42
  tail call void @verifier.assume(i1 %_7) #4
  tail call void @seahorn.fail() #4
  br label %entry.split

entry.split:                                      ; preds = %entry
  ret i32 42
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i64(i8* nocapture writeonly, i8, i64, i32, i1) #0

declare void @verifier.assert(i1)

attributes #0 = { argmemonly nounwind }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn }
attributes #3 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"clang version 5.0.2 (tags/RELEASE_502/final)"}
!4 = !{!5, !5, i64 0}
!5 = !{!"int", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
