; RUN: %seabmc "%s" 2>&1 | %oc %s
; wide integers
; CHECK: ^sat$
;; ModuleID = '/var/folders/_j/1_4mrwbs7y16zbvj79vwvhdc0000gn/T/sea-HWKLid/t5.pp.ms.o.ul.cut.bc'
source_filename = "/tmp/t5.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.13.0"

@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind ssp uwtable
define private i32 @orig.main() local_unnamed_addr #0 {
  call void @seahorn.fn.enter() #3
  %1 = alloca [2 x i32], align 8
  %2 = alloca [2 x i32], align 8
  %3 = bitcast [2 x i32]* %1 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %3) #3
  %4 = bitcast [2 x i32]* %1 to i64*
  store i64 1005022347387, i64* %4, align 8
  %5 = bitcast [2 x i32]* %2 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %5) #3
  %6 = bitcast [2 x i32]* %2 to i64*
  store i64 100742752912665, i64* %6, align 8
  %7 = getelementptr inbounds [2 x i32], [2 x i32]* %1, i32 0, i32 0
  %8 = getelementptr inbounds [2 x i32], [2 x i32]* %2, i32 0, i32 0
  call void @seahorn.fn.enter() #3
  %9 = getelementptr inbounds i32, i32* %7, i32 1
  %10 = getelementptr inbounds i32, i32* %8, i32 1
  %11 = load i32, i32* %9, align 4, !tbaa !4
  store i32 %11, i32* %10, align 4, !tbaa !4
  %12 = getelementptr inbounds [2 x i32], [2 x i32]* %2, i32 0, i32 1
  %13 = load i32, i32* %12, align 4, !tbaa !4
  %14 = icmp eq i32 %13, 234
  br i1 %14, label %15, label %16

; <label>:15:                                     ; preds = %0
  call void @verifier.error() #3
  unreachable

; <label>:16:                                     ; preds = %0
  %17 = bitcast [2 x i32]* %2 to i8*
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %17) #3
  %18 = bitcast [2 x i32]* %1 to i8*
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %18) #3
  ret i32 0
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #1

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #2

declare void @seahorn.fn.enter() local_unnamed_addr

declare void @verifier.assert(i1)

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #0 {
entry:
  %0 = alloca [2 x i32], align 8
  %1 = alloca [2 x i32], align 8
  call void @seahorn.fn.enter() #3
  %2 = bitcast [2 x i32]* %0 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %2) #3
  %3 = bitcast [2 x i32]* %0 to i64*
  store i64 1005022347387, i64* %3, align 8
  %4 = bitcast [2 x i32]* %1 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %4) #3
  %5 = bitcast [2 x i32]* %1 to i64*
  store i64 100742752912665, i64* %5, align 8
  %6 = getelementptr inbounds [2 x i32], [2 x i32]* %0, i32 0, i32 0
  %7 = getelementptr inbounds [2 x i32], [2 x i32]* %1, i32 0, i32 0
  call void @seahorn.fn.enter() #3
  %8 = getelementptr inbounds i32, i32* %6, i32 1
  %9 = getelementptr inbounds i32, i32* %7, i32 1
  %10 = load i32, i32* %8, align 4, !tbaa !4
  store i32 %10, i32* %9, align 4, !tbaa !4
  %11 = getelementptr inbounds [2 x i32], [2 x i32]* %1, i32 0, i32 1
  %12 = load i32, i32* %11, align 4, !tbaa !4
  %13 = icmp eq i32 %12, 234
  call void @verifier.assume(i1 %13)
  br label %14

; <label>:14:                                     ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %14
  call void @seahorn.fail()
  ret i32 42
}

declare i1 @nondet.bool()

attributes #0 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { noreturn }
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
