; RUN: %seabmc --lower-gv-init=false "%s" 2>&1 | %oc %s
; RUN: %seabmc --lower-gv-init=false --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
; ModuleID = 'tmp_bc/code.pp.ms.o.ul.cut.bc'
source_filename = "code.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@un_init = internal unnamed_addr global i1 false, align 4
@llvm.used = appending global [4 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*)], section "llvm.metadata"

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
  store i1 false, i1* @un_init, align 4
  tail call void @seahorn.fn.enter() #3
  tail call void @seahorn.fn.enter() #3
  %.b1 = load i1, i1* @un_init, align 4
  br i1 %.b1, label %get_y.exit.i, label %0

; <label>:0:                                      ; preds = %entry
  store i1 true, i1* @un_init, align 4
  br label %get_y.exit.i

get_y.exit.i:                                     ; preds = %0, %entry
  %1 = tail call i32 @nd() #3
  %2 = icmp eq i32 %1, 0
  br i1 %2, label %verifier.error, label %.lr.ph

.lr.ph:                                           ; preds = %get_y.exit.i
  %.b = load i1, i1* @un_init, align 4
  %3 = tail call i32 @nd() #3
  %4 = icmp eq i32 %3, 0
  tail call void @verifier.assume(i1 %4) #3
  br label %verifier.error

verifier.error:                                   ; preds = %.lr.ph, %get_y.exit.i
  %.0.i.lcssa = phi i1 [ false, %get_y.exit.i ], [ %.b, %.lr.ph ]
  tail call void @verifier.assume.not(i1 %.0.i.lcssa) #3
  tail call void @seahorn.fail() #3
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
