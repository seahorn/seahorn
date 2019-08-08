; RUN: %seabmc "%s" --horn-bv2-word-size=1 2>&1 | %oc %s
; RUN: %seabmc "%s" --horn-bv2-word-size=4 2>&1 | %oc %s
; RUN: %seabmc "%s" --horn-bv2-word-size=8 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --horn-gsa --log=opsem3 "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --horn-vcgen-use-ite --log=opsem3 "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --horn-gsa --horn-vcgen-use-ite --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^unsat$
;; ModuleID = '/tmp/sea-E9l3Jc/ggg.pp.ms.o.ul.cut.bc'
source_filename = "/tmp/ggg.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-unknown-linux-gnu"

@_br_1 = internal unnamed_addr global i32 0, align 4
@.str = private unnamed_addr constant [5 x i8] c"abc\0A\00", align 1
@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter() local_unnamed_addr

declare void @verifier.assert(i1)

; Function Attrs: nounwind
define i32 @main() local_unnamed_addr #0 {
entry:
  store i32 0, i32* @_br_1, align 4
  call void @seahorn.fn.enter() #2
  call void @seahorn.fn.enter() #2
  br label %0

; <label>:0:                                      ; preds = %entry
  %.0.i.i = phi i8* [ getelementptr inbounds ([5 x i8], [5 x i8]* @.str, i32 0, i32 0), %entry ]
  call void @seahorn.fn.enter() #2
  %1 = load i8, i8* %.0.i.i, align 1, !tbaa !3
  %2 = icmp eq i8 %1, 10
  %3 = zext i1 %2 to i32
  %4 = icmp eq i32 %3, 0
  br i1 %4, label %5, label %foo.exit.i

; <label>:5:                                      ; preds = %0
  %6 = load i32, i32* @_br_1, align 4, !tbaa !6
  %7 = add nsw i32 %6, 1
  store i32 %7, i32* @_br_1, align 4, !tbaa !6
  %8 = getelementptr inbounds i8, i8* %.0.i.i, i32 1
  br i1 true, label %12, label %fake_latch_exit

foo.exit.i:                                       ; preds = %39, %30, %21, %12, %0
  %9 = load i32, i32* @_br_1, align 4, !tbaa !6
  %10 = icmp eq i32 %9, 3
  call void @verifier.assume.not(i1 %10)
  br label %11

; <label>:11:                                     ; preds = %foo.exit.i
  br label %verifier.error

verifier.error:                                   ; preds = %11
  call void @seahorn.fail()
  ret i32 42

fake_latch_exit:                                  ; preds = %44, %35, %26, %17, %5
  unreachable

; <label>:12:                                     ; preds = %5
  call void @seahorn.fn.enter() #2
  %13 = load i8, i8* %8, align 1, !tbaa !3
  %14 = icmp eq i8 %13, 10
  %15 = zext i1 %14 to i32
  %16 = icmp eq i32 %15, 0
  br i1 %16, label %17, label %foo.exit.i

; <label>:17:                                     ; preds = %12
  %18 = load i32, i32* @_br_1, align 4, !tbaa !6
  %19 = add nsw i32 %18, 1
  store i32 %19, i32* @_br_1, align 4, !tbaa !6
  %20 = getelementptr inbounds i8, i8* %8, i32 1
  br i1 true, label %21, label %fake_latch_exit

; <label>:21:                                     ; preds = %17
  call void @seahorn.fn.enter() #2
  %22 = load i8, i8* %20, align 1, !tbaa !3
  %23 = icmp eq i8 %22, 10
  %24 = zext i1 %23 to i32
  %25 = icmp eq i32 %24, 0
  br i1 %25, label %26, label %foo.exit.i

; <label>:26:                                     ; preds = %21
  %27 = load i32, i32* @_br_1, align 4, !tbaa !6
  %28 = add nsw i32 %27, 1
  store i32 %28, i32* @_br_1, align 4, !tbaa !6
  %29 = getelementptr inbounds i8, i8* %20, i32 1
  br i1 true, label %30, label %fake_latch_exit

; <label>:30:                                     ; preds = %26
  call void @seahorn.fn.enter() #2
  %31 = load i8, i8* %29, align 1, !tbaa !3
  %32 = icmp eq i8 %31, 10
  %33 = zext i1 %32 to i32
  %34 = icmp eq i32 %33, 0
  br i1 %34, label %35, label %foo.exit.i

; <label>:35:                                     ; preds = %30
  %36 = load i32, i32* @_br_1, align 4, !tbaa !6
  %37 = add nsw i32 %36, 1
  store i32 %37, i32* @_br_1, align 4, !tbaa !6
  %38 = getelementptr inbounds i8, i8* %29, i32 1
  br i1 true, label %39, label %fake_latch_exit

; <label>:39:                                     ; preds = %35
  call void @seahorn.fn.enter() #2
  %40 = load i8, i8* %38, align 1, !tbaa !3
  %41 = icmp eq i8 %40, 10
  %42 = zext i1 %41 to i32
  %43 = icmp eq i32 %42, 0
  br i1 %43, label %44, label %foo.exit.i

; <label>:44:                                     ; preds = %39
  %45 = load i32, i32* @_br_1, align 4, !tbaa !6
  %46 = add nsw i32 %45, 1
  store i32 %46, i32* @_br_1, align 4, !tbaa !6
  %47 = getelementptr inbounds i8, i8* %38, i32 1
  call void @verifier.assume.not(i1 true)
  br label %fake_latch_exit
}

declare i1 @nondet.bool()

attributes #0 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 5.0.1 (tags/RELEASE_501/final)"}
!3 = !{!4, !4, i64 0}
!4 = !{!"omnipotent char", !5, i64 0}
!5 = !{!"Simple C/C++ TBAA"}
!6 = !{!7, !7, i64 0}
!7 = !{!"int", !4, i64 0}
