; RUN: %seabmc "%s" 2>&1 | %oc %s
;; Handling bswap intrinsic
; CHECK: ^unsat$
;; ModuleID = '/tmp/sea-UbOU1E/t6.pp.ms.o.ul.cut.bc'
source_filename = "/tmp/t6.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-unknown-linux-gnu"

@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

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

; Function Attrs: nounwind readnone speculatable
declare i32 @llvm.bswap.i32(i32) #3

declare void @verifier.assert(i1)

; Function Attrs: nounwind
define i32 @main() local_unnamed_addr #0 {
entry:
  %0 = alloca i64, align 8
  call void @seahorn.fn.enter() #4
  %1 = bitcast i64* %0 to i8*
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %1) #4
  call void @seahorn.fn.enter() #4
  store i64 -77195985809396258, i64* %0, align 8, !tbaa !3
  call void @seahorn.fn.enter() #4
  %2 = load i64, i64* %0, align 4, !tbaa !3
  %3 = trunc i64 %2 to i32
  call void @seahorn.fn.enter() #4
  %4 = call i32 @llvm.bswap.i32(i32 %3) #4
  %5 = icmp eq i32 %4, -559038737
  call void @verifier.assume.not(i1 %5)
  br label %6

; <label>:6:                                      ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %6
  call void @seahorn.fail()
  ret i32 42
}

declare i1 @nondet.bool()

attributes #0 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { noreturn }
attributes #3 = { nounwind readnone speculatable }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 5.0.1 (tags/RELEASE_501/final)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"long long", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
