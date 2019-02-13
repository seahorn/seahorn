; Confuse pointers to the stack. Write to them. Expect possible aliasing.
; RUN: %seabmc "%s" 2>&1 | %oc %s
; CHECK: ^sat$
; ModuleID = 'ptr.01.ll'
source_filename = "../test/bmc/test-bmc-1.false.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.13.0"

declare i32 @nd() local_unnamed_addr #0

declare void @verifier.assume(i1)
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @use(i32*, i32*) local_unnamed_addr #0

; Function Attrs: nounwind ssp uwtable
define i32 @main() local_unnamed_addr #2 {
entry:
  %x = alloca i32, align 4
  %y = alloca i32, align 4
  call void @use(i32* %x, i32* %y)
  %nd1 = call i32 @nd()
  %cmp = icmp eq i32 %nd1, 5
  %z = select i1 %cmp, i32* %x, i32* %y
  store i32 32, i32* %z
  %cmp2 = icmp ne i32 %nd1, 3
  %z2 = select i1 %cmp2, i32* %x, i32* %y
  store i32 42, i32* %z2
  %a = load i32, i32* %x
  %b = load i32, i32* %y
  %sum = add nsw i32 %b, %a
  %c = icmp eq i32 %sum, 74
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
