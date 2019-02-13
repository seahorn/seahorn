; RUN: %seabmc "%s" 2>&1 | %oc %s
; CHECK: ^unsat$
; ModuleID = '/tmp/sea-nX_rmb/mem.pp.ms.bc'
source_filename = "/tmp/mem.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-unknown-linux-gnu"


; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1) #1

declare void @use(i32*) local_unnamed_addr #2

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #3

declare void @seahorn.fn.enter() local_unnamed_addr

declare void @verifier.assert(i1)

; Function Attrs: nounwind
define i32 @main() local_unnamed_addr #0 {
entry:
  %malloc1.i = alloca [16 x i8], align 1
  %0 = bitcast [16 x i8]* %malloc1.i to i8*
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %0)
  call void @seahorn.fn.enter() #4
  %1 = getelementptr inbounds [16 x i8], [16 x i8]* %malloc1.i, i32 0, i32 0
  call void @llvm.memset.p0i8.i32(i8* %1, i8 12, i32 16, i32 4, i1 false) #4
  %2 = getelementptr inbounds [16 x i8], [16 x i8]* %malloc1.i, i32 0, i32 12
  %3 = bitcast i8* %2 to i32*
  %4 = load i32, i32* %3, align 4, !tbaa !3
  %5 = icmp eq i32 %4, 202116108  ; 0x0C0C0C0C
  call void @verifier.assume.not(i1 %5)
  br label %6

; <label>:6:                                      ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %6
  call void @seahorn.fail()
  ret i32 42
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #1

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #1

declare i1 @nondet.bool()

attributes #0 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 5.0.1 (tags/RELEASE_501/final)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
