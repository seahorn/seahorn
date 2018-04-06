; RUN: %seainspect %s -mem-dot -sea-dsa-stats --sea-dsa-dot-outdir=%T/structs.local.ll
; RUN: %cmp-graphs %tests/structs.local.entry.mem.dot %T/structs.local.ll/entry.mem.dot both | OutputCheck %s -d --comment=";"
; CHECK: ^OK$

; ModuleID = 'structs.local.c.ll'
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

%struct.A = type { i32, float }
%struct.B = type { float*, %struct.A* }

@entry.a = private unnamed_addr constant %struct.A { i32 1, float 0x40090A3D80000000 }, align 4

; Function Attrs: nounwind uwtable
define void @entry() #0 {
bb:
  %a = alloca %struct.A, align 4
  %f = alloca float, align 4
  %b = alloca %struct.B, align 8
  %ii = alloca i32*, align 8
  %tmp = bitcast %struct.A* %a to i8*
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %tmp, i8* bitcast (%struct.A* @entry.a to i8*), i64 8, i32 4, i1 false)
  store float 4.200000e+01, float* %f, align 4
  %tmp1 = getelementptr inbounds %struct.B, %struct.B* %b, i32 0, i32 0
  store float* %f, float** %tmp1, align 8
  %tmp2 = getelementptr inbounds %struct.B, %struct.B* %b, i32 0, i32 1
  store %struct.A* %a, %struct.A** %tmp2, align 8
  %tmp3 = getelementptr inbounds %struct.B, %struct.B* %b, i32 0, i32 1
  %tmp4 = load %struct.A*, %struct.A** %tmp3, align 8
  %tmp5 = getelementptr inbounds %struct.A, %struct.A* %tmp4, i32 0, i32 0
  store i32* %tmp5, i32** %ii, align 8
  ret void
}

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture, i8* nocapture readonly, i64, i32, i1) #1

attributes #0 = { nounwind uwtable "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }

!llvm.ident = !{!0}

!0 = !{!"clang version 3.8.1 (tags/RELEASE_381/final)"}
