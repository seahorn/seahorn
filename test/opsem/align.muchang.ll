; RUN: %seabmc "%s" 2>&1 | %oc %s
; playing with alignment. Two variables are created, 
; checks that the third bit differs between them.
; CHECK: ^sat$
;; ModuleID = '/var/folders/_j/1_4mrwbs7y16zbvj79vwvhdc0000gn/T/sea-1nJpV2/align.test.pp.ms.bc'
source_filename = "align.test.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.13.0"

@foo.last_align = internal unnamed_addr global i32 -1, align 4
@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*)], section "llvm.metadata"

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #0

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #0

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #2 {
entry:
  %0 = alloca i32, align 4
  %1 = alloca i32, align 4
  store i32 -1, i32* @foo.last_align, align 4
  tail call void @seahorn.fn.enter() #3
  tail call void @seahorn.fn.enter() #3
  %2 = bitcast i32* %1 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* nonnull %2) #3
  store i32 0, i32* %1, align 4, !tbaa !4
  %3 = ptrtoint i32* %1 to i32
  %4 = and i32 %3, 12
  %5 = load i32, i32* @foo.last_align, align 4, !tbaa !4
  %6 = icmp slt i32 %5, 0
  br i1 %6, label %7, label %8

; <label>:7:                                      ; preds = %entry
  store i32 %4, i32* @foo.last_align, align 4, !tbaa !4
  br label %foo.exit.i

; <label>:8:                                      ; preds = %entry
  %9 = icmp eq i32 %4, %5
  br i1 %9, label %foo.exit.i, label %verifier.error

foo.exit.i:                                       ; preds = %8, %7
  call void @llvm.lifetime.end.p0i8(i64 4, i8* nonnull %2) #3
  call void @seahorn.fn.enter() #3
  %10 = bitcast i32* %0 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* nonnull %10) #3
  store i32 0, i32* %0, align 4, !tbaa !4
  %11 = ptrtoint i32* %0 to i32
  %12 = and i32 %11, 12
  %13 = load i32, i32* @foo.last_align, align 4, !tbaa !4
  %14 = icmp slt i32 %13, 0
  call void @verifier.assume.not(i1 %14) #3
  %15 = load i32, i32* @foo.last_align, align 4, !tbaa !4
  %16 = icmp eq i32 %12, %15
  call void @verifier.assume.not(i1 %16) #3
  br label %verifier.error

verifier.error:                                   ; preds = %8, %foo.exit.i
  call void @seahorn.fail() #3
  ret i32 42
}

attributes #0 = { argmemonly nounwind }
attributes #1 = { noreturn }
attributes #2 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

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
