; RUN: %seainspect %s -mem-dot -sea-dsa-stats --sea-dsa-dot-outdir=%T/params.ll
; RUN: %cmp-graphs %tests/params.entry.mem.dot %T/params.ll/entry.mem.dot both | OutputCheck %s -d --comment=";"
; CHECK: ^OK$

; ModuleID = 'param.c.ll'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

; Function Attrs: nounwind uwtable
define void @entry(i8** %argv) #0 {
bb:
  %tmp = alloca i8**, align 8
  %str = alloca i8*, align 8
  store i8** %argv, i8*** %tmp, align 8
  %tmp1 = load i8**, i8*** %tmp, align 8
  %tmp2 = getelementptr inbounds i8*, i8** %tmp1, i64 0
  %tmp3 = load i8*, i8** %tmp2, align 8
  store i8* %tmp3, i8** %str, align 8
  ret void
}

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
