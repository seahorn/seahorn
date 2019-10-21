; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s
;; testing extracting form const struct with global pointer type fields
; CHECK: ^unsat$
; ModuleID = 'test-insert-value'
source_filename = "/tmp/st.c"
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.13.0"

%struct.s = type { i16*, i32 } ; struct with a ptr to i16 and a i32 int
@g.ptr =  internal unnamed_addr global i16 42, align 4
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()


; Function Attrs: noreturn
declare void @verifier.error() #0

; Function Attrs: noinline nounwind ssp uwtable
define i32 @main() local_unnamed_addr #2 {
entry:
  ;; %v1 = load i16, i16* @g.ptr
  %st = insertvalue %struct.s undef, i16* @g.ptr, 0
  %v2.p = extractvalue %struct.s %st, 0
  %v2 = load i16, i16* %v2.p
  %cond = icmp eq i16 42, %v2
  call void @verifier.assume.not(i1 %cond)
  br label %verifier.error

verifier.error:                                   ; preds = %entry
  call void @seahorn.fail()
  br label %verifier.error.split

verifier.error.split:                             ; preds = %verifier.error
  ret i32 42
}

attributes #0 = { noreturn }
attributes #1 = { argmemonly nounwind }
attributes #2 = { noinline nounwind ssp uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="penryn" "target-features"="+cx16,+fxsr,+mmx,+sse,+sse2,+sse3,+sse4.1,+ssse3,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!0, !1, !2}
!llvm.ident = !{!3}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{i32 7, !"PIC Level", i32 2}
!3 = !{!"clang version 5.0.2 (tags/RELEASE_502/final)"}
