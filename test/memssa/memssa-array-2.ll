; RUN: %horn --horn-bmc --keep-shadows=true --horn-sea-dsa --sea-dsa=ci \
; RUN:       -horn-inter-proc -horn-sem-lvl=mem --horn-gsa=false \
; RUN:       --horn-step=large --horn-bv2=true --horn-stats \
; RUN:       --log="shadow_verbose" --log="shadow_optimizer" \
; RUN:       "%s" 2>&1 | OutputCheck %s --comment=";"

; CHECK-L: Module before shadow insertion:
; CHECK-L: ret i32 42

; This is case is not optimized yet -- we don't look thru the memPhi / memGamma.
; CHECK-L: MemSSA optimizer: 0 use(s) solved.

; CHECK-L: Module after shadow insertion:
; CHECK-L:  ret i32 42

; ModuleID = '/tmp/sea-TPe4qz/memssa-array-2.pp.ms.o.ul.cut.o.bc'
source_filename = "/media/nvme/projects/seahorn-5/test/memssa/memssa-array-2.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@llvm.used = appending global [12 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

declare i32* @freshInt() local_unnamed_addr #0

declare i32 @nd() local_unnamed_addr #0

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
  %2 = call i32 @nd() #3
  %3 = icmp eq i32 %2, 0
  %4 = select i1 %3, i32* %1, i32* %0
  store i32 42, i32* %4, align 4, !tbaa !3
  %5 = call i32 @nd() #3
  %6 = icmp eq i32 %5, 0
  %7 = select i1 %6, i32* %1, i32* %0
  store i32 13, i32* %7, align 4, !tbaa !3
  %8 = call i32 @nd() #3
  %9 = icmp eq i32 %8, 0
  br i1 %9, label %12, label %10

; <label>:10:                                     ; preds = %entry
  %11 = getelementptr inbounds i32, i32* %0, i32 1
  store i32 33, i32* %11, align 4, !tbaa !3
  br label %12

; <label>:12:                                     ; preds = %10, %entry
  %13 = getelementptr inbounds i32, i32* %0, i32 1
  %14 = load i32, i32* %13, align 4, !tbaa !3
  %15 = load i32, i32* %7, align 4, !tbaa !3
  %16 = add nsw i32 %14, %15
  %17 = icmp sgt i32 %16, 20
  call void @verifier.assume.not(i1 %17)
  br label %18

; <label>:18:                                     ; preds = %12
  br label %verifier.error

verifier.error:                                   ; preds = %18
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

