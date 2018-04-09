; RUN: %seainspect %s -mem-dot -sea-dsa-stats --sea-dsa-dot-outdir=%T/int2ptr.ll
; RUN: %cmp-graphs %tests/int2ptr.entry.mem.dot %T/int2ptr.ll/entry.mem.dot both | OutputCheck %s -d --comment=";"
; CHECK: ^OK$

; ModuleID = 'int2ptr.c.ll'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind uwtable
define void @entry() #0 {
bb:
  %a = alloca i32, align 4
  %ptr = alloca i32*, align 8
  %tmp = call i32 @nd()
  store i32 %tmp, i32* %a, align 4
  %tmp1 = load i32, i32* %a, align 4
  %tmp2 = sext i32 %tmp1 to i64
  %tmp3 = inttoptr i64 %tmp2 to i32*
  store i32* %tmp3, i32** %ptr, align 8
  ret void
}

declare i32 @nd() #1

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
