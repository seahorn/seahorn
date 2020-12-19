; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s
;; Check inline asm of bswap is handled
; CHECK: ^sat$

; ModuleID = 'bswap.bswapl.inline.asm_sat.ll'
source_filename = "../opsem2/bswap/bswap-pen-inline-asm_sat.c"
target datalayout = "e-m:e-p:32:32-p270:32:32-p271:32:32-p272:64:64-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

declare dso_local i32 @nd_uint32_t() local_unnamed_addr #0

declare void @verifier.assume(i1) #1
declare void @verifier.assume.not(i1) #1
declare void @seahorn.fail() #1

; Function Attrs: nounwind
define dso_local i32 @main(i32 %0, i8** nocapture readnone %1) local_unnamed_addr #4 {
entry:
  %2 = tail call i32 @nd_uint32_t() #5
  %3 = tail call i32 @nd_uint32_t() #5
  %4 = icmp eq i32 %2, %3
  tail call void @verifier.assume(i1 %4) #5
  %5 = tail call i32 asm "bswapl ${0:q}", "=r,0,~{dirflag},~{fpsr},~{flags}"(i32 %2) #6, !srcloc !3
  %6 = tail call i32 asm "bswapl ${0:q}", "=r,0,~{dirflag},~{fpsr},~{flags}"(i32 %3) #6, !srcloc !4
  %7 = icmp eq i32 %5, %6
  tail call void @verifier.assume(i1 %7)
  tail call void @seahorn.fail()
  ret i32 42
}

attributes #0 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cx8,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { inaccessiblememonly nofree norecurse nounwind }
attributes #2 = { inaccessiblememonly nofree norecurse noreturn nounwind }
attributes #3 = { inaccessiblememonly }
attributes #4 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="i686" "target-features"="+cx8,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { nounwind }
attributes #6 = { nounwind readnone }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"Ubuntu clang version 10.0.1-++20201112101950+ef32c611aa2-1~exp1~20201112092551.202"}
!3 = !{i32 -2147367762}
!4 = !{i32 -2147367553}
