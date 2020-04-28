; RUN: %horn --horn-bmc --keep-shadows=true  --sea-dsa=ci \
; RUN:       -horn-inter-proc -horn-sem-lvl=mem --horn-gsa=false \
; RUN:       --horn-step=large --horn-bv2=true --horn-stats \
; RUN:       --log="shadow_verbose" --log="shadow_optimizer" \
; RUN:       "%s" 2>&1 | OutputCheck %s --comment=";"

; CHECK-L: Module before shadow insertion:
; CHECK-L: ret i32 42

; CHECK-L: MemSSA optimizer: 2 use(s) solved.

; CHECK-L: Module after shadow insertion:
; CHECK-L:  ret i32 42

; ModuleID = '/tmp/sea-JwPcwz/memssa-array-1.pp.ms.o.ul.cut.o.bc'
source_filename = "/media/nvme/projects/seahorn-5/test/memssa/memssa-array-1.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@llvm.used = appending global [12 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

declare i32* @freshInt() local_unnamed_addr #0

declare void @sea_dsa_alias(i32*, i32*) local_unnamed_addr #0

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind
define i32 @main() local_unnamed_addr #2 {
entry:
  call void @seahorn.fn.enter() #3
  %0 = call i32* @freshInt() #3
  %1 = call i32* @freshInt() #3
  call void @sea_dsa_alias(i32* %0, i32* %1) #3
  store i32 33, i32* %0, align 4, !tbaa !3
  %2 = getelementptr inbounds i32, i32* %0, i32 1
  store i32 44, i32* %2, align 4, !tbaa !3
  store i32 52, i32* %1, align 4, !tbaa !3
  %3 = load i32, i32* %0, align 4, !tbaa !3
  %4 = getelementptr inbounds i32, i32* %0, i32 1
  %5 = load i32, i32* %4, align 4, !tbaa !3
  %6 = add nsw i32 %3, %5
  %7 = icmp eq i32 %6, 96
  call void @verifier.assume.not(i1 %7)
  br label %8

; <label>:8:                                      ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %8
  call void @seahorn.fail()
  ret i32 42
}

attributes #0 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 5.0.1-4 (tags/RELEASE_501/final)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"int", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
