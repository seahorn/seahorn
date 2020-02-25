; RUN: %seabmc "%s" 2>&1 | %oc %s

; CHECK: ^unsat$
; ModuleID = '../test/bmc/test_binary_operator.c'
source_filename = "../test/bmc/test_binary_operator.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"
declare void @verifier.assume(i1)
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()

declare {i32, i1} @llvm.uadd.with.overflow.i32(i32 %a, i32 %b)

; Function Attrs: noreturn
declare void @verifier.error() #1

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #2 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  store i32 4294967295, i32* %x, align 4
  store i32 1, i32* %y, align 4
  %z1 = load i32, i32* %x, align 4
  %z2 = load i32, i32* %y, align 4
  %res = call {i32, i1} @llvm.uadd.with.overflow.i32(i32 %z2, i32 %z1)

  %add1 = extractvalue {i32, i1} %res, 0
  %compare = icmp eq i32 %add1, 0
  call void @verifier.assume(i1 %compare)
  
  %add2 = extractvalue {i32, i1} %res, 1
  %compare2 = icmp eq i1 %add2, 1
 
  ; create a condition where both the operation and carry bit are correct.
  %cond = and i1 %compare, %compare2 
  ; %cond should never be satisfied
 
  call void @verifier.assume.not(i1 %compare) 
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
attributes #0 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"clang version 5.0.2 (tags/RELEASE_502/final)"}
