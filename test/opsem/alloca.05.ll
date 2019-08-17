; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^unsat$
; ModuleID = 'alloca.01.ll'
source_filename = "../test/bmc/test-bmc-1.false.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.13.0"

declare i128 @nd.i128() local_unnamed_addr #0

declare void @verifier.assume(i1)
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @use(i128*, i128*) local_unnamed_addr #0

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #2 {
entry:
  %x = alloca i128, align 4
  %y = alloca i128, align 4
  call void @use(i128* %x, i128* %y)
  %nd1 = call i128 @nd.i128()
  %v1 = icmp eq i128 %nd1, 4
  call void @verifier.assume(i1 %v1)
  %nd2 = call i128 @nd.i128()
  %v2 = icmp eq i128 %nd2, 5
  call void @verifier.assume(i1 %v2)
  store i128 %nd1, i128* %x
  store i128 %nd2, i128* %y
  %a = load i128, i128* %x
  %b = load i128, i128* %y
  %c = icmp ne i128 %a, %b
  call void @verifier.assume.not(i1 %c)
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 42
}


attributes #0 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn }
attributes #2 = { nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"clang version 5.0.2 (tags/RELEASE_502/final)"}
