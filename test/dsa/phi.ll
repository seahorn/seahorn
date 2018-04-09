; RUN: %seainspect %s -mem-dot -sea-dsa-stats --sea-dsa-dot-outdir=%T/phi.ll
; RUN: %cmp-graphs %tests/phi.entry.mem.dot %T/phi.ll/entry.mem.dot both | OutputCheck %s -d --comment=";"
; CHECK: ^OK$

; ModuleID = 'phi.c.ll'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind uwtable
define i32 @entry(i32 %c) #0 {
bb:
  %tmp = alloca i32, align 4
  %a = alloca i32, align 4
  %b = alloca i32, align 4
  %res = alloca i32*, align 8
  store i32 %c, i32* %tmp, align 4
  store i32 1, i32* %a, align 4
  store i32 2, i32* %b, align 4
  %tmp1 = load i32, i32* %tmp, align 4
  %tmp2 = icmp ne i32 %tmp1, 0
  br i1 %tmp2, label %bb3, label %bb4

bb3:                                              ; preds = %bb
  br label %bb5

bb4:                                              ; preds = %bb
  br label %bb5

bb5:                                              ; preds = %bb4, %bb3
  %tmp6 = phi i32* [ %a, %bb3 ], [ %b, %bb4 ]
  store i32* %tmp6, i32** %res, align 8
  %tmp7 = load i32*, i32** %res, align 8
  %tmp8 = load i32, i32* %tmp7, align 4
  ret i32 %tmp8
}

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
