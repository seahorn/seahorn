; RUN: %seabmc "%s" 2>&1 | %oc %s
; CHECK: ^unsat$
; ModuleID = '/var/folders/_j/1_4mrwbs7y16zbvj79vwvhdc0000gn/T/sea-sytGp6/mem.02.pp.ms.bc'
source_filename = "/tmp/mem.02.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.13.0"

@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind ssp uwtable

declare void @use(i32*, i32*) local_unnamed_addr #1

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #2

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: argmemonly nounwind
declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1) #3

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i32(i8* nocapture writeonly, i8* nocapture readonly, i32, i32, i1) #3

declare void @verifier.assert(i1)

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #0 {
entry:
  %malloc2.i = alloca [32 x i8], align 1
  %malloc13.i = alloca [32 x i8], align 1
  %0 = bitcast [32 x i8]* %malloc2.i to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* %0)
  %1 = bitcast [32 x i8]* %malloc13.i to i8*
  call void @llvm.lifetime.start.p0i8(i64 32, i8* %1)
  call void @seahorn.fn.enter() #4
  %2 = getelementptr inbounds [32 x i8], [32 x i8]* %malloc2.i, i32 0, i32 0
  call void @llvm.memset.p0i8.i32(i8* %2, i8 12, i32 32, i32 4, i1 false) #4
  %3 = getelementptr inbounds [32 x i8], [32 x i8]* %malloc13.i, i32 0, i32 0
  %4 = getelementptr inbounds [32 x i8], [32 x i8]* %malloc2.i, i32 0, i32 0
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* %3, i8* %4, i32 32, i32 4, i1 false) #4
  %5 = getelementptr inbounds [32 x i8], [32 x i8]* %malloc13.i , i32 0, i32 12
  %6 = bitcast i8* %5 to i32*
  %7 = load i32, i32* %6, align 4, !tbaa !4
  %8 = icmp eq i32 %7, 202116108
  call void @verifier.assume.not(i1 %8)
  br label %9

; <label>:9:                                      ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %9
  call void @seahorn.fail()
  ret i32 42
}

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #3

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.end.p0i8(i64, i8* nocapture) #3

declare i1 @nondet.bool()

attributes #0 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn }
attributes #3 = { argmemonly nounwind }
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
