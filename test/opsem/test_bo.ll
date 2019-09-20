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
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  store i32 0, i32* %1, align 4
  %10 = bitcast i32* %2 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %10) #4
  %11 = bitcast i32* %3 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %11) #4
  store i32 10, i32* %2, align 4, !tbaa !5
  store i32 5, i32* %3, align 4, !tbaa !5
  %12 = call i32 @nd()
  %13 = icmp ne i32 %12, 0
  br i1 %13, label %14, label %18

; <label>:14:                                     ; preds = %0
  %15 = load i32, i32* %2, align 4, !tbaa !5
  %16 = load i32, i32* %3, align 4, !tbaa !5
  %17 = sub nsw i32 %15, %16
  store i32 %17, i32* %2, align 4, !tbaa !5
  br label %18

; <label>:18:                                     ; preds = %14, %0
  %19 = load i32, i32* %2, align 4, !tbaa !5
  %20 = icmp eq i32 %19, 5
  br i1 %20, label %22, label %21

; <label>:21:                                     ; preds = %18
  call void @__VERIFIER_error() #5
  unreachable

; <label>:22:                                     ; preds = %18
  store i32 5, i32* %2, align 4, !tbaa !5
  store i32 9, i32* %3, align 4, !tbaa !5
  %23 = call i32 @nd()
  %24 = icmp ne i32 %23, 0
  br i1 %24, label %25, label %29

; <label>:25:                                     ; preds = %22
  %26 = load i32, i32* %2, align 4, !tbaa !5
  %27 = load i32, i32* %3, align 4, !tbaa !5
  %28 = xor i32 %26, %27
  store i32 %28, i32* %2, align 4, !tbaa !5
  br label %29

; <label>:29:                                     ; preds = %25, %22
  %30 = load i32, i32* %2, align 4, !tbaa !5
  %31 = icmp eq i32 %30, 12
  br i1 %31, label %33, label %32

; <label>:32:                                     ; preds = %29
  call void @__VERIFIER_error() #5
  unreachable

; <label>:33:                                     ; preds = %29
  store i32 7, i32* %2, align 4, !tbaa !5
  store i32 5, i32* %3, align 4, !tbaa !5
  %34 = call i32 @nd()
  %35 = icmp ne i32 %34, 0
  br i1 %35, label %36, label %40

; <label>:36:                                     ; preds = %33
  %37 = load i32, i32* %2, align 4, !tbaa !5
  %38 = load i32, i32* %3, align 4, !tbaa !5
  %39 = mul nsw i32 %37, %38
  store i32 %39, i32* %2, align 4, !tbaa !5
  br label %40

; <label>:40:                                     ; preds = %36, %33
  %41 = load i32, i32* %2, align 4, !tbaa !5
  %42 = icmp eq i32 %41, 35
  br i1 %42, label %44, label %43

; <label>:43:                                     ; preds = %40
  call void @__VERIFIER_error() #5
  unreachable

; <label>:44:                                     ; preds = %40
  store i32 9, i32* %2, align 4, !tbaa !5
  store i32 4, i32* %3, align 4, !tbaa !5
  %45 = bitcast i32* %4 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %45) #4
  %46 = bitcast i32* %5 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %46) #4
  %47 = call i32 @nd()
  %48 = icmp ne i32 %47, 0
  br i1 %48, label %49, label %56

; <label>:49:                                     ; preds = %44
  %50 = load i32, i32* %2, align 4, !tbaa !5
  %51 = load i32, i32* %3, align 4, !tbaa !5
  %52 = sdiv i32 %50, %51
  store i32 %52, i32* %4, align 4, !tbaa !5
  %53 = load i32, i32* %2, align 4, !tbaa !5
  %54 = load i32, i32* %3, align 4, !tbaa !5
  %55 = srem i32 %53, %54
  store i32 %55, i32* %5, align 4, !tbaa !5
  br label %56

; <label>:56:                                     ; preds = %49, %44
  %57 = load i32, i32* %4, align 4, !tbaa !5
  %58 = icmp eq i32 %57, 2
  br i1 %58, label %60, label %59

; <label>:59:                                     ; preds = %56
  call void @__VERIFIER_error() #5
  unreachable

; <label>:60:                                     ; preds = %56
  %61 = load i32, i32* %5, align 4, !tbaa !5
  %62 = icmp eq i32 %61, 1
  br i1 %62, label %64, label %63

; <label>:63:                                     ; preds = %60
  call void @__VERIFIER_error() #5
  unreachable

; <label>:64:                                     ; preds = %60
  %65 = bitcast i32* %6 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %65) #4
  %66 = bitcast i32* %7 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %66) #4
  %67 = bitcast i32* %8 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %67) #4
  %68 = bitcast i32* %9 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %68) #4
  store i32 10, i32* %8, align 4, !tbaa !5
  store i32 3, i32* %9, align 4, !tbaa !5
  %69 = call i32 @nd()
  %70 = icmp ne i32 %69, 0
  br i1 %70, label %71, label %78

; <label>:71:                                     ; preds = %64
  %72 = load i32, i32* %8, align 4, !tbaa !5
  %73 = load i32, i32* %9, align 4, !tbaa !5
  %74 = udiv i32 %72, %73
  store i32 %74, i32* %6, align 4, !tbaa !5
  %75 = load i32, i32* %8, align 4, !tbaa !5
  %76 = load i32, i32* %9, align 4, !tbaa !5
  %77 = urem i32 %75, %76
  store i32 %77, i32* %7, align 4, !tbaa !5
  br label %78

; <label>:78:                                     ; preds = %71, %64
  %79 = load i32, i32* %6, align 4, !tbaa !5
  %80 = icmp eq i32 %79, 3
  br i1 %80, label %82, label %81

; <label>:81:                                     ; preds = %78
  call void @__VERIFIER_error() #5
  unreachable

; <label>:82:                                     ; preds = %78
  %83 = load i32, i32* %7, align 4, !tbaa !5
  %84 = icmp eq i32 %83, 1
  br i1 %84, label %86, label %85

; <label>:85:                                     ; preds = %82
  call void @__VERIFIER_error() #5
  unreachable

; <label>:86:                                     ; preds = %82
  %87 = bitcast i32* %9 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %87) #4
  %88 = bitcast i32* %8 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %88) #4
  %89 = bitcast i32* %7 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %89) #4
  %90 = bitcast i32* %6 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %90) #4
  %91 = bitcast i32* %5 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %91) #4
  %92 = bitcast i32* %4 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %92) #4
  %93 = bitcast i32* %3 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %93) #4
  %94 = bitcast i32* %2 to i8*
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %94) #4
  ret i32 0
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #1

declare i32 @nd() #2

; Function Attrs: noreturn
declare void @__VERIFIER_error() #3

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #1

attributes #0 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sahf,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }
attributes #5 = { noreturn }

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
