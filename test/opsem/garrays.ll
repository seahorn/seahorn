; RUN: %seabmc "%s" 2>&1 | %oc %s
; CHECK: ^unsat$
; ModuleID = '/tmp/sea-c4RgIb/garrays.pp.ms.bc'
source_filename = "garrays.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@yyyyyy = internal global [3 x i32] [i32 1, i32 2, i32 3], align 4
@yyyyyyy = internal global i32* getelementptr inbounds ([3 x i32], [3 x i32]* @yyyyyy, i32 0, i32 0), align 4
@zzzzzz = internal global [2 x [2 x i32]] [[2 x i32] [i32 4, i32 5], [2 x i32] [i32 6, i32 7]], align 4
@zzzzzzz = internal global i32* getelementptr inbounds ([2 x [2 x i32]], [2 x [2 x i32]]* @zzzzzz, i32 0, i32 0, i32 0), align 4
@.str = private unnamed_addr constant [4 x i8] c"abc\00", align 1
@wwwwwww = internal global i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), align 4
@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind
define private i32 @orig.main() local_unnamed_addr #0 {
  store i32* getelementptr inbounds ([3 x i32], [3 x i32]* @yyyyyy, i32 0, i32 0), i32** @yyyyyyy, align 4
  store i32* getelementptr inbounds ([2 x [2 x i32]], [2 x [2 x i32]]* @zzzzzz, i32 0, i32 0, i32 0), i32** @zzzzzzz, align 4
  store i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i8** @wwwwwww, align 4
  call void @seahorn.fn.enter() #3
  %1 = call i32 bitcast (i32 (...)* @unknown1 to i32 ()*)() #3
  %2 = icmp eq i32 %1, 0
  br i1 %2, label %29, label %3

; <label>:3:                                      ; preds = %0
  %4 = load i32*, i32** @yyyyyyy, align 4, !tbaa !3
  %5 = getelementptr inbounds i32, i32* %4, i32 1
  %6 = load i32, i32* %5, align 4, !tbaa !7
  %7 = icmp eq i32 %6, 2
  %8 = select i1 %7, i32 2, i32 1
  %9 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %10 = getelementptr inbounds i32, i32* %9, i32 3
  %11 = load i32, i32* %10, align 4, !tbaa !7
  %12 = icmp eq i32 %11, 7
  %13 = select i1 %12, i32 2, i32 1
  %14 = load i8*, i8** @wwwwwww, align 4, !tbaa !3
  %15 = getelementptr inbounds i8, i8* %14, i32 1
  %16 = load i8, i8* %15, align 1, !tbaa !9
  %17 = icmp eq i8 %16, 98
  %18 = add nuw nsw i32 %8, 1
  %19 = load i32*, i32** @yyyyyyy, align 4, !tbaa !3
  %20 = getelementptr inbounds i32, i32* %19, i32 2
  store i32 %18, i32* %20, align 4, !tbaa !7
  %21 = add nuw nsw i32 %13, 1
  %22 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %23 = getelementptr inbounds i32, i32* %22, i32 2
  store i32 %21, i32* %23, align 4, !tbaa !7
  %24 = add nuw nsw i32 %8, %13
  %25 = getelementptr inbounds i32, i32* %22, i32 1
  store i32 %24, i32* %25, align 4, !tbaa !7
  %26 = select i1 %17, i8 3, i8 2
  %27 = load i8*, i8** @wwwwwww, align 4, !tbaa !3
  %28 = getelementptr inbounds i8, i8* %27, i32 2
  store i8 %26, i8* %28, align 1, !tbaa !9
  br label %29

; <label>:29:                                     ; preds = %3, %0
  %30 = load i32*, i32** @yyyyyyy, align 4, !tbaa !3
  %31 = getelementptr inbounds i32, i32* %30, i32 2
  %32 = load i32, i32* %31, align 4, !tbaa !7
  %33 = icmp sgt i32 %32, 0
  br i1 %33, label %35, label %34

; <label>:34:                                     ; preds = %29
  call void @verifier.error() #3
  unreachable

; <label>:35:                                     ; preds = %29
  %36 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %37 = getelementptr inbounds i32, i32* %36, i32 1
  %38 = load i32, i32* %37, align 4, !tbaa !7
  %39 = icmp sgt i32 %38, 0
  br i1 %39, label %41, label %40

; <label>:40:                                     ; preds = %35
  call void @verifier.error() #3
  unreachable

; <label>:41:                                     ; preds = %35
  %42 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %43 = getelementptr inbounds i32, i32* %42, i32 2
  %44 = load i32, i32* %43, align 4, !tbaa !7
  %45 = icmp sgt i32 %44, 0
  br i1 %45, label %47, label %46

; <label>:46:                                     ; preds = %41
  call void @verifier.error() #3
  unreachable

; <label>:47:                                     ; preds = %41
  %48 = load i8*, i8** @wwwwwww, align 4, !tbaa !3
  %49 = getelementptr inbounds i8, i8* %48, i32 2
  %50 = load i8, i8* %49, align 1, !tbaa !9
  %51 = icmp sgt i8 %50, 0
  br i1 %51, label %53, label %52

; <label>:52:                                     ; preds = %47
  call void @verifier.error() #3
  unreachable

; <label>:53:                                     ; preds = %47
  call void @f(i32** nonnull @yyyyyyy) #3
  call void @f(i32** nonnull @zzzzzzz) #3
  call void @f(i32** bitcast (i8** @wwwwwww to i32**)) #3
  ret i32 0
}

declare i32 @unknown1(...) local_unnamed_addr #1

declare void @f(i32**) local_unnamed_addr #1

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
  store i32* getelementptr inbounds ([3 x i32], [3 x i32]* @yyyyyy, i32 0, i32 0), i32** @yyyyyyy, align 4
  store i32* getelementptr inbounds ([2 x [2 x i32]], [2 x [2 x i32]]* @zzzzzz, i32 0, i32 0, i32 0), i32** @zzzzzzz, align 4
  store i8* getelementptr inbounds ([4 x i8], [4 x i8]* @.str, i32 0, i32 0), i8** @wwwwwww, align 4
  call void @seahorn.fn.enter() #3
  %0 = call i32 bitcast (i32 (...)* @unknown1 to i32 ()*)() #3
  %1 = icmp eq i32 %0, 0
  br i1 %1, label %28, label %2

; <label>:2:                                      ; preds = %entry
  %3 = load i32*, i32** @yyyyyyy, align 4, !tbaa !3
  %4 = getelementptr inbounds i32, i32* %3, i32 1
  %5 = load i32, i32* %4, align 4, !tbaa !7
  %6 = icmp eq i32 %5, 2
  %7 = select i1 %6, i32 2, i32 1
  %8 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %9 = getelementptr inbounds i32, i32* %8, i32 3
  %10 = load i32, i32* %9, align 4, !tbaa !7
  %11 = icmp eq i32 %10, 7
  %12 = select i1 %11, i32 2, i32 1
  %13 = load i8*, i8** @wwwwwww, align 4, !tbaa !3
  %14 = getelementptr inbounds i8, i8* %13, i32 1
  %15 = load i8, i8* %14, align 1, !tbaa !9
  %16 = icmp eq i8 %15, 98
  %17 = add nuw nsw i32 %7, 1
  %18 = load i32*, i32** @yyyyyyy, align 4, !tbaa !3
  %19 = getelementptr inbounds i32, i32* %18, i32 2
  store i32 %17, i32* %19, align 4, !tbaa !7
  %20 = add nuw nsw i32 %12, 1
  %21 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %22 = getelementptr inbounds i32, i32* %21, i32 2
  store i32 %20, i32* %22, align 4, !tbaa !7
  %23 = add nuw nsw i32 %7, %12
  %24 = getelementptr inbounds i32, i32* %21, i32 1
  store i32 %23, i32* %24, align 4, !tbaa !7
  %25 = select i1 %16, i8 3, i8 2
  %26 = load i8*, i8** @wwwwwww, align 4, !tbaa !3
  %27 = getelementptr inbounds i8, i8* %26, i32 2
  store i8 %25, i8* %27, align 1, !tbaa !9
  br label %28

; <label>:28:                                     ; preds = %2, %entry
  %29 = load i32*, i32** @yyyyyyy, align 4, !tbaa !3
  %30 = getelementptr inbounds i32, i32* %29, i32 2
  %31 = load i32, i32* %30, align 4, !tbaa !7
  %32 = icmp sgt i32 %31, 0
  br i1 %32, label %34, label %33

; <label>:33:                                     ; preds = %28
  br label %verifier.error

; <label>:34:                                     ; preds = %28
  %35 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %36 = getelementptr inbounds i32, i32* %35, i32 1
  %37 = load i32, i32* %36, align 4, !tbaa !7
  %38 = icmp sgt i32 %37, 0
  br i1 %38, label %40, label %39

; <label>:39:                                     ; preds = %34
  br label %verifier.error

; <label>:40:                                     ; preds = %34
  %41 = load i32*, i32** @zzzzzzz, align 4, !tbaa !3
  %42 = getelementptr inbounds i32, i32* %41, i32 2
  %43 = load i32, i32* %42, align 4, !tbaa !7
  %44 = icmp sgt i32 %43, 0
  br i1 %44, label %46, label %45

; <label>:45:                                     ; preds = %40
  br label %verifier.error

; <label>:46:                                     ; preds = %40
  %47 = load i8*, i8** @wwwwwww, align 4, !tbaa !3
  %48 = getelementptr inbounds i8, i8* %47, i32 2
  %49 = load i8, i8* %48, align 1, !tbaa !9
  %50 = icmp sgt i8 %49, 0
  call void @verifier.assume.not(i1 %50)
  br label %51

; <label>:51:                                     ; preds = %46
  br label %verifier.error

verifier.error:                                   ; preds = %51, %45, %39, %33
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
!7 = !{!8, !8, i64 0}
!8 = !{!"int", !5, i64 0}
!9 = !{!5, !5, i64 0}
