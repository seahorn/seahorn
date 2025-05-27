; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
; ModuleID = 'fsh.c'
source_filename = "fsh.c"
target datalayout = "e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-f64:32:64-f80:32-n8:16:32-S128"
target triple = "x86_64-pc-linux-gnu"

@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*)], section "llvm.metadata"

declare i64 @llvm.fshr.i64(i64 noundef, i64 noundef, i64 noundef) local_unnamed_addr #0

declare i64 @llvm.fshl.i64(i64 noundef, i64 noundef, i64 noundef) local_unnamed_addr #0

declare zeroext i8 @llvm.fshr.i8(i8 noundef zeroext, i8 noundef zeroext, i8 noundef zeroext) local_unnamed_addr #0

declare zeroext i8 @llvm.fshl.i8(i8 noundef zeroext, i8 noundef zeroext, i8 noundef zeroext) local_unnamed_addr #0

declare zeroext i16 @llvm.fshr.i16(i16 noundef zeroext, i16 noundef zeroext, i16 noundef zeroext) local_unnamed_addr #0

declare zeroext i16 @llvm.fshl.i16(i16 noundef zeroext, i16 noundef zeroext, i16 noundef zeroext) local_unnamed_addr #0

; Function Attrs: inaccessiblememonly nofree norecurse noreturn nounwind
declare void @verifier.error() #2

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @verifier.assume(i1) #3

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @verifier.assume.not(i1) #3

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @seahorn.fail() #3

; Function Attrs: inaccessiblememonly
declare void @seahorn.fn.enter() local_unnamed_addr #4


; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #6 {
entry:
  tail call void @seahorn.fn.enter() #7
  tail call void @seahorn.fn.enter() #7
  tail call void @seahorn.fn.enter() #7
  %0 = tail call zeroext i16 @llvm.fshl.i16(i16 noundef zeroext -3856, i16 noundef zeroext 4080, i16 noundef zeroext 5)
  %1 = icmp eq i16 %0, 7681
  br i1 %1, label %2, label %verifier.error

2:                                                ; preds = %entry
  tail call void @seahorn.fn.enter() #7
  %3 = tail call zeroext i16 @llvm.fshr.i16(i16 noundef zeroext -3856, i16 noundef zeroext 4080, i16 noundef zeroext 3)
  %4 = icmp eq i16 %3, 510
  br i1 %4, label %5, label %verifier.error

5:                                                ; preds = %2
  tail call void @seahorn.fn.enter() #7
  %6 = tail call zeroext i8 @llvm.fshl.i8(i8 noundef zeroext -1, i8 noundef zeroext 0, i8 noundef zeroext 15)
  %7 = icmp eq i8 %6, -128
  br i1 %7, label %8, label %verifier.error

8:                                                ; preds = %5
  tail call void @seahorn.fn.enter() #7
  %9 = tail call zeroext i8 @llvm.fshl.i8(i8 noundef zeroext 15, i8 noundef zeroext 15, i8 noundef zeroext 11)
  %10 = icmp eq i8 %9, 120
  br i1 %10, label %11, label %verifier.error

11:                                               ; preds = %8
  tail call void @seahorn.fn.enter() #7
  %12 = tail call zeroext i8 @llvm.fshl.i8(i8 noundef zeroext 0, i8 noundef zeroext -1, i8 noundef zeroext 8)
  %13 = icmp eq i8 %12, 0
  br i1 %13, label %14, label %verifier.error

14:                                               ; preds = %11
  tail call void @seahorn.fn.enter() #7
  %15 = tail call zeroext i8 @llvm.fshr.i8(i8 noundef zeroext -1, i8 noundef zeroext 0, i8 noundef zeroext 15)
  %16 = icmp eq i8 %15, -2
  br i1 %16, label %17, label %verifier.error

17:                                               ; preds = %14
  tail call void @seahorn.fn.enter() #7
  %18 = tail call zeroext i8 @llvm.fshr.i8(i8 noundef zeroext 15, i8 noundef zeroext 15, i8 noundef zeroext 11)
  %19 = icmp eq i8 %18, -31
  br i1 %19, label %20, label %verifier.error

20:                                               ; preds = %17
  tail call void @seahorn.fn.enter() #7
  %21 = tail call zeroext i8 @llvm.fshr.i8(i8 noundef zeroext 0, i8 noundef zeroext -1, i8 noundef zeroext 8)
  %22 = icmp eq i8 %21, -1
  br i1 %22, label %23, label %verifier.error

23:                                               ; preds = %20
  tail call void @seahorn.fn.enter() #7
  %24 = tail call i64 @llvm.fshl.i64(i64 noundef 1311768467294899695, i64 noundef -81986143110479071, i64 noundef 16)
  %25 = icmp ne i64 %24, 6230889152035946204
  br i1 %25, label %26, label %verifier.error

26:                                               ; preds = %23
  tail call void @seahorn.fn.enter() #7
  %27 = tail call i64 @llvm.fshr.i64(i64 noundef 1311768467294899695, i64 noundef -81986143110479071, i64 noundef 16)
  %28 = icmp eq i64 %27, -3607384552533031067
  br i1 %28, label %29, label %verifier.error

29:                                               ; preds = %26
  tail call void @seahorn.fn.enter() #7
  %30 = tail call i64 @llvm.fshl.i64(i64 noundef -4294967296, i64 noundef 4294967295, i64 noundef 32)
  %31 = icmp eq i64 %30, 0
  br i1 %31, label %32, label %verifier.error

32:                                               ; preds = %29
  tail call void @seahorn.fn.enter() #7
  %33 = tail call i64 @llvm.fshr.i64(i64 noundef -4294967296, i64 noundef 4294967295, i64 noundef 32)
  %34 = icmp eq i64 %33, 0
  tail call void @verifier.assume.not(i1 %34)
  br label %verifier.error

verifier.error:                                   ; preds = %32, %29, %26, %23, %20, %17, %14, %11, %8, %5, %2, %entry
  tail call void @seahorn.fail()
  ret i32 42
}

attributes #0 = { "frame-pointer"="none" "no-builtin-memcpy" "no-builtin-memmove" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #1 = { alwaysinline mustprogress nofree nounwind readonly uwtable willreturn "frame-pointer"="none" "min-legal-vector-width"="0" "no-builtin-memcpy" "no-builtin-memmove" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #2 = { inaccessiblememonly nofree norecurse noreturn nounwind }
attributes #3 = { inaccessiblememonly nofree norecurse nounwind }
attributes #4 = { inaccessiblememonly }
attributes #5 = { mustprogress nofree nosync nounwind readnone speculatable willreturn }
attributes #6 = { nounwind uwtable "frame-pointer"="none" "min-legal-vector-width"="0" "no-builtin-memcpy" "no-builtin-memmove" "no-trapping-math"="true" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "tune-cpu"="generic" }
attributes #7 = { nounwind }
attributes #8 = { nounwind "no-builtin-memcpy" "no-builtin-memmove" }
