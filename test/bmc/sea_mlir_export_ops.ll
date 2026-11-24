; sea-mlir export (--horn-sea-mlir-export-only, no sea-vc needed): zero
; global initializers as one sea.memset, a byte-splat initializer as one
; sea.memset, one sea.ptr.index per GEP (a constant-only inbounds GEP has
; no indices), alignment on memory ops and objects, llvm.cttz / ctlz /
; bitreverse in existing sea ops, a comment-only barrier asm as a no-op.
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG: comment-only body and a memory clobber treated as a no-op
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK-DAG: sea.global @"zarr" size 64 align 16
; CHECK-DAG: sea.global @"splat" size 8 align 8
; CHECK-DAG: %[[Z:v[0-9]+]] = sea.const 0 : i8
; CHECK-DAG: %[[SEVEN:v[0-9]+]] = sea.const 7 : i8
; CHECK-DAG: sea.memset %{{v[0-9]+}}[%{{v[0-9]+}}], %[[Z]], %{{v[0-9]+}} inplace
; CHECK-DAG: sea.memset %{{v[0-9]+}}[%{{v[0-9]+}}], %[[SEVEN]], %{{v[0-9]+}} inplace
; CHECK: sea.ptr.index %{{v[0-9]+}} [%{{v[0-9]+}}] strides [4] offset 0 inbounds
; CHECK: sea.store {{.*}} align 4
; CHECK: sea.ptr.index %{{v[0-9]+}} [] strides [] offset 8 inbounds
; CHECK: sea.store {{.*}} align 8
; CHECK: sea.select {{.*}} loc("tz")
; CHECK: sea.select {{.*}} loc("lz")
; CHECK: sea.concat {{.*}} loc("br")
; CHECK-NOT: asm
; CHECK: sea.assert
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.S = type { i32, i64 }

@zarr = global [16 x i32] zeroinitializer, align 16
@splat = global [8 x i8] c"\07\07\07\07\07\07\07\07", align 8
@s = global %struct.S zeroinitializer, align 8

declare i32 @nd()
declare void @verifier.assume(i1)
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare i32 @llvm.cttz.i32(i32, i1)
declare i32 @llvm.ctlz.i32(i32, i1)
declare i32 @llvm.bitreverse.i32(i32)

define i32 @main() {
entry:
  %i = call i32 @nd()
  %ic = icmp ult i32 %i, 8
  call void @verifier.assume(i1 %ic)
  %i64 = zext i32 %i to i64
  %p = getelementptr inbounds [16 x i32], ptr @zarr, i64 0, i64 %i64
  %x = call i32 @nd()
  store i32 %x, ptr %p, align 4
  %pb = getelementptr inbounds %struct.S, ptr @s, i64 0, i32 1
  %xl = sext i32 %x to i64
  store i64 %xl, ptr %pb, align 8
  %tz = call i32 @llvm.cttz.i32(i32 %x, i1 false)
  %lz = call i32 @llvm.ctlz.i32(i32 %x, i1 false)
  %br = call i32 @llvm.bitreverse.i32(i32 %x)
  call void asm sideeffect "# FD_COMPILER_MFENCE()", "~{memory},~{dirflag},~{fpsr},~{flags}"()
  %v = load i32, ptr %p, align 4
  %ps = getelementptr inbounds [8 x i8], ptr @splat, i64 0, i64 %i64
  %sv = load i8, ptr %ps, align 1
  %c1 = icmp eq i32 %v, %x
  %c2 = icmp ule i32 %tz, 32
  %c3 = icmp ule i32 %lz, 32
  %c4 = icmp ne i32 %br, 7
  %c5 = icmp eq i8 %sv, 7
  %a1 = and i1 %c1, %c2
  %a2 = and i1 %a1, %c3
  %a3 = or i1 %a2, %c4
  %a4 = and i1 %a3, %c5
  call void @verifier.assume.not(i1 %a4)
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
