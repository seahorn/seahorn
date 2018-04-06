; RUN: %seainspect %s -mem-dot -sea-dsa-stats --sea-dsa-dot-outdir=%T-globals
; RUN: %cmp-graphs %tests/globals.entry.mem.dot %T-globals/entry.mem.dot both | OutputCheck %s -d --comment=";"
; CHECK: ^OK$

@a = common global i32 0, align 4
@b = common global i32 0, align 4
@c = common global i32 0, align 4
@f = common global float 0.000000e+00, align 4
@g = common global float 0.000000e+00, align 4
@h = common global float 0.000000e+00, align 4
@v = common global i32 (...)* null, align 8

; Function Attrs: nounwind uwtable
define i32 @entry(i32 %arc, i8** %argv) #0 {
bb:
  %tmp1 = alloca i32, align 4
  %tmp2 = alloca i8**, align 8
  %aa = alloca i32*, align 8
  %fp = alloca float*, align 8
  %gp = alloca float*, align 8
  %tmp = alloca float**, align 8
  %str = alloca i8*, align 8
  store i32 %arc, i32* %tmp1, align 4
  store i8** %argv, i8*** %tmp2, align 8
  store i32 1, i32* @a, align 4
  %tmp3 = load i32, i32* @a, align 4
  %tmp4 = add nsw i32 %tmp3, 1
  store i32 %tmp4, i32* @b, align 4
  %tmp5 = load i32, i32* @b, align 4
  %tmp6 = add nsw i32 %tmp5, 1
  store i32 %tmp6, i32* @c, align 4
  store float 4.000000e+00, float* @f, align 4
  %tmp7 = load float, float* @f, align 4
  %tmp8 = fadd float %tmp7, 1.000000e+00
  store float %tmp8, float* @g, align 4
  %tmp9 = load float, float* @g, align 4
  %tmp10 = fadd float %tmp9, 1.000000e+00
  store float %tmp10, float* @h, align 4
  store i32 (...)* bitcast (i32 (i32, i8**)* @entry to i32 (...)*), i32 (...)** @v, align 8
  store i32* @a, i32** %aa, align 8
  store float* @f, float** %fp, align 8
  store float* @g, float** %gp, align 8
  store float** null, float*** %tmp, align 8
  %tmp11 = load i32, i32* @a, align 4
  %tmp12 = icmp ne i32 %tmp11, 0
  br i1 %tmp12, label %bb13, label %bb14

bb13:                                             ; preds = %bb
  store float** %fp, float*** %tmp, align 8
  br label %bb15

bb14:                                             ; preds = %bb
  store float** %gp, float*** %tmp, align 8
  br label %bb15

bb15:                                             ; preds = %bb14, %bb13
  %tmp16 = load i8**, i8*** %tmp2, align 8
  %tmp17 = getelementptr inbounds i8*, i8** %tmp16, i64 0
  %tmp18 = load i8*, i8** %tmp17, align 8
  store i8* %tmp18, i8** %str, align 8
  ret i32 0
}

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}

