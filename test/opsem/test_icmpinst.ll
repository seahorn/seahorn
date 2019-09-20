; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

; Function Attrs: nounwind ssp uwtable
define i32 @main() #0 {
  %1 = alloca i32, align 4
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %6 = bitcast i32* %2 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %6) #3
  %7 = bitcast i32* %3 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %7) #3
  %8 = bitcast i32* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %8) #3
  %9 = bitcast i32* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %9) #3
  store i32 8, i32* %4, align 4, !tbaa !5
  store i32 5, i32* %5, align 4, !tbaa !5
  store i32 10, i32* %2, align 4, !tbaa !5
  store i32 5, i32* %3, align 4, !tbaa !5
  %10 = load i32, i32* %2, align 4, !tbaa !5
  %11 = load i32, i32* %3, align 4, !tbaa !5
  %12 = icmp sgt i32 %10, %11
  br i1 %12, label %14, label %13

; <label>:13:                                     ; preds = %0
  call void @__VERIFIER_error() #4
  unreachable

; <label>:14:                                     ; preds = %0
  %15 = load i32, i32* %2, align 4, !tbaa !5
  %16 = load i32, i32* %3, align 4, !tbaa !5
  %17 = icmp sge i32 %15, %16
  br i1 %17, label %19, label %18

; <label>:18:                                     ; preds = %14
  call void @__VERIFIER_error() #4
  unreachable

; <label>:19:                                     ; preds = %14
  %20 = load i32, i32* %4, align 4, !tbaa !5
  %21 = load i32, i32* %5, align 4, !tbaa !5
  %22 = icmp ugt i32 %20, %21
  br i1 %22, label %24, label %23

; <label>:23:                                     ; preds = %19
  call void @__VERIFIER_error() #4
  unreachable

; <label>:24:                                     ; preds = %19
  %25 = load i32, i32* %4, align 4, !tbaa !5
  %26 = load i32, i32* %5, align 4, !tbaa !5
  %27 = icmp uge i32 %25, %26
  br i1 %27, label %29, label %28

; <label>:28:                                     ; preds = %24
  call void @__VERIFIER_error() #4
  unreachable

; <label>:29:                                     ; preds = %24
  store i32 6, i32* %4, align 4, !tbaa !5
  store i32 9, i32* %5, align 4, !tbaa !5
  store i32 8, i32* %2, align 4, !tbaa !5
  store i32 14, i32* %3, align 4, !tbaa !5
  %30 = load i32, i32* %2, align 4, !tbaa !5
  %31 = load i32, i32* %3, align 4, !tbaa !5
  %32 = icmp slt i32 %30, %31
  br i1 %32, label %34, label %33

; <label>:33:                                     ; preds = %29
  call void @__VERIFIER_error() #4
  unreachable

; <label>:34:                                     ; preds = %29
  %35 = load i32, i32* %2, align 4, !tbaa !5
  %36 = load i32, i32* %3, align 4, !tbaa !5
  %37 = icmp sle i32 %35, %36
  br i1 %37, label %39, label %38

; <label>:38:                                     ; preds = %34
  call void @__VERIFIER_error() #4
  unreachable

; <label>:39:                                     ; preds = %34
  %40 = load i32, i32* %4, align 4, !tbaa !5
  %41 = load i32, i32* %5, align 4, !tbaa !5
  %42 = icmp ult i32 %40, %41
  br i1 %42, label %44, label %43

; <label>:43:                                     ; preds = %39
  call void @__VERIFIER_error() #4
  unreachable

; <label>:44:                                     ; preds = %39
  %45 = load i32, i32* %4, align 4, !tbaa !5
  %46 = load i32, i32* %5, align 4, !tbaa !5
  %47 = icmp ule i32 %45, %46
  br i1 %47, label %49, label %48

; <label>:48:                                     ; preds = %44
  call void @__VERIFIER_error() #4
  unreachable

; <label>:49:                                     ; preds = %44
  %50 = bitcast i32* %5 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %50) #3
  %51 = bitcast i32* %4 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %51) #3
  %52 = bitcast i32* %3 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %52) #3
  %53 = bitcast i32* %2 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %53) #3
  ret i32 0
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #1

; Function Attrs: noreturn
declare void @__VERIFIER_error() #2

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #1

attributes #0 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }
attributes #4 = { noreturn }

!llvm.module.flags = !{!0, !1, !2, !3}
!llvm.ident = !{!4}

!0 = !{i32 2, !"SDK Version", [2 x i32] [i32 10, i32 14]}
!1 = !{i32 1, !"NumRegisterParameters", i32 0}
!2 = !{i32 1, !"wchar_size", i32 4}
!3 = !{i32 7, !"PIC Level", i32 2}
!4 = !{!"Apple LLVM version 10.0.1 (clang-1001.0.46.4)"}
!5 = !{!6, !6, i64 0}
!6 = !{!"int", !7, i64 0}
!7 = !{!"omnipotent char", !8, i64 0}
!8 = !{!"Simple C/C++ TBAA"}
