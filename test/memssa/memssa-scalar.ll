; RUN: %horn --horn-bmc --keep-shadows=true --horn-sea-dsa --sea-dsa=ci \
; RUN:       -horn-inter-proc -horn-sem-lvl=mem --horn-gsa=false \
; RUN:       --horn-step=large --horn-bv2=true --horn-stats \
; RUN:       --log="shadow_verbose" --log="shadow_optimizer" \
; RUN:       "%s" 2>&1 | OutputCheck %s --comment=";"

; CHECK-L: Module before shadow insertion:
; CHECK-L: ret i32 42

; CHECK-L: MemSSA optimizer: 1 use(s) solved.

; CHECK-L: Module after shadow insertion:
; CHECK-L:  %sm = call i32 @shadow.mem.store(i32 0, i32 %sm2, i8* null), !shadow.mem
; CHECK-L:  %sm1 = call i32 @shadow.mem.store(i32 0, i32 %sm, i8* null), !shadow.mem
; CHECK-L:  call void @shadow.mem.load(i32 0, i32 %sm, i8* null), !shadow.mem
; CHECK-L:  ret i32 42

; ModuleID = '/tmp/sea-ArTKhT/memssa-scalar.pp.ms.o.ul.cut.o.bc'
source_filename = "/media/nvme/projects/seahorn-5/test/memssa/memssa-scalar.c"
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
  %0 = alloca i32, align 4
  %1 = alloca i32, align 4
  call void @seahorn.fn.enter() #3
  call void @sea_dsa_alias(i32* %0, i32* %1) #3
  store i32 11, i32* %0, align 4, !tbaa !3
  store i32 12, i32* %1, align 4, !tbaa !3
  %2 = load i32, i32* %0, align 4, !tbaa !3
  %3 = icmp eq i32 %2, 11
  call void @verifier.assume.not(i1 %3)
  br label %4

; <label>:4:                                      ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %4
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
