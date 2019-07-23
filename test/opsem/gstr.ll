; RUN: %seabmc "%s" 2>&1 | %oc %s
; CHECK: ^unsat$
; ModuleID = '/tmp/sea-rHRc0a/gstr.pp.ms.bc'
source_filename = "gstr.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@.str = private unnamed_addr constant [4 x i8] c"abc\00", align 1
@yyyyyyy = internal global i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), align 4
@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind
define private i32 @orig.main() local_unnamed_addr #0 {
  store i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i8** @yyyyyyy, align 4
  call void @seahorn.fn.enter() #3
  %1 = call i32 bitcast (i32 (...)* @unknown1 to i32 ()*)() #3
  %2 = icmp eq i32 %1, 0
  br i1 %2, label %10, label %3

; <label>:3:                                      ; preds = %0
  %4 = load i8*, i8** @yyyyyyy, align 4, !tbaa !3
  %5 = getelementptr inbounds i8, i8* %4, i32 1
  %6 = load i8, i8* %5, align 1, !tbaa !7
  %7 = icmp eq i8 %6, 98
  %8 = select i1 %7, i8 3, i8 2
  %9 = getelementptr inbounds i8, i8* %4, i32 2
  store i8 %8, i8* %9, align 1, !tbaa !7
  br label %10

; <label>:10:                                     ; preds = %3, %0
  %11 = load i8*, i8** @yyyyyyy, align 4, !tbaa !3
  %12 = getelementptr inbounds i8, i8* %11, i32 2
  %13 = load i8, i8* %12, align 1, !tbaa !7
  %14 = icmp sgt i8 %13, 0
  br i1 %14, label %16, label %15

; <label>:15:                                     ; preds = %10
  call void @verifier.error() #3
  unreachable

; <label>:16:                                     ; preds = %10
  call void @f(i8** nonnull @yyyyyyy) #3
  ret i32 0
}

declare i32 @unknown1(...) local_unnamed_addr #1

declare void @f(i8**) local_unnamed_addr #1

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #2

declare void @seahorn.fn.enter() local_unnamed_addr

declare void @verifier.assert(i1)

; Function Attrs: nounwind
define i32 @main() local_unnamed_addr #0 {
entry:
  store i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i8** @yyyyyyy, align 4
  call void @seahorn.fn.enter() #3
  %0 = call i32 bitcast (i32 (...)* @unknown1 to i32 ()*)() #3
  %1 = icmp eq i32 %0, 0
  br i1 %1, label %9, label %2

; <label>:2:                                      ; preds = %entry
  %3 = load i8*, i8** @yyyyyyy, align 4, !tbaa !3
  %4 = getelementptr inbounds i8, i8* %3, i32 1
  %5 = load i8, i8* %4, align 1, !tbaa !7
  %6 = icmp eq i8 %5, 98
  %7 = select i1 %6, i8 3, i8 2
  %8 = getelementptr inbounds i8, i8* %3, i32 2
  store i8 %7, i8* %8, align 1, !tbaa !7
  br label %9

; <label>:9:                                      ; preds = %2, %entry
  %10 = load i8*, i8** @yyyyyyy, align 4, !tbaa !3
  %11 = getelementptr inbounds i8, i8* %10, i32 2
  %12 = load i8, i8* %11, align 1, !tbaa !7
  %13 = icmp sgt i8 %12, 0
  call void @verifier.assume.not(i1 %13)
  br label %14

; <label>:14:                                     ; preds = %9
  br label %verifier.error

verifier.error:                                   ; preds = %14
  call void @seahorn.fail()
  ret i32 42
}

declare i1 @nondet.bool()

attributes #0 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"any pointer", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = !{!5, !5, i64 0}
