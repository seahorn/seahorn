; sea-mlir export: C++ operator new / new[] (also nothrow and
; std::align_val_t forms) is sea.malloc, operator delete / delete[] (also
; sized and std::align_val_t forms) is sea.free, as malloc / free. A constant
; std::align_val_t is the object's alignment; otherwise it is 16, as malloc.
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG-NOT: Error
; LOG: std::align_val_t that is not a constant power of two
; LOG-NOT: Error
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK: sea.malloc %{{v[0-9]+}} align 16 [{{[0-9]+}}] : i64 -> !sea.ptr<64> loc("a")
; CHECK: sea.malloc %{{v[0-9]+}} align 16 [{{[0-9]+}}] : i64 -> !sea.ptr<64> loc("b")
; CHECK: sea.malloc %{{v[0-9]+}} align 16 [{{[0-9]+}}] : i64 -> !sea.ptr<64> loc("c")
; CHECK: sea.malloc %{{v[0-9]+}} align 64 [{{[0-9]+}}] : i64 -> !sea.ptr<64> loc("d")
; CHECK: sea.malloc %{{v[0-9]+}} align 32 [{{[0-9]+}}] : i64 -> !sea.ptr<64> loc("e")
; CHECK: sea.malloc %{{v[0-9]+}} align 16 [{{[0-9]+}}] : i64 -> !sea.ptr<64> loc("f")
; SeaHorn's pipeline deletes the _ZdlPv / _ZdaPv calls (LLVM knows them);
; the other forms reach the export:
; CHECK-COUNT-4: sea.free %{{v[0-9]+}} : !sea.ptr<64>
; CHECK-NOT: sea.free
; CHECK: sea.assert
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@_ZSt7nothrow = external global i8, align 1

declare i64 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare ptr @_Znwm(i64)
declare ptr @_Znam(i64)
declare ptr @_ZnwmRKSt9nothrow_t(i64, ptr)
declare ptr @_ZnwmSt11align_val_t(i64, i64)
declare ptr @_ZnamSt11align_val_tRKSt9nothrow_t(i64, i64, ptr)
declare void @_ZdlPv(ptr)
declare void @_ZdlPvm(ptr, i64)
declare void @_ZdaPv(ptr)
declare void @_ZdlPvRKSt9nothrow_t(ptr, ptr)
declare void @_ZdlPvSt11align_val_t(ptr, i64)
declare void @_ZdaPvmSt11align_val_t(ptr, i64, i64)

define i32 @main() {
entry:
  %al = call i64 @nd()
  %a = call ptr @_Znwm(i64 4)
  store i32 1, ptr %a, align 4
  %b = call ptr @_Znam(i64 16)
  %b3 = getelementptr inbounds i32, ptr %b, i64 3
  store i32 2, ptr %b3, align 4
  %c = call ptr @_ZnwmRKSt9nothrow_t(i64 8, ptr @_ZSt7nothrow)
  store i32 3, ptr %c, align 4
  %d = call ptr @_ZnwmSt11align_val_t(i64 64, i64 64)
  store i32 4, ptr %d, align 64
  %e = call ptr @_ZnamSt11align_val_tRKSt9nothrow_t(i64 32, i64 32, ptr @_ZSt7nothrow)
  store i32 5, ptr %e, align 32
  %f = call ptr @_ZnwmSt11align_val_t(i64 8, i64 %al)
  store i32 6, ptr %f, align 4
  %va = load i32, ptr %a, align 4
  %vb = load i32, ptr %b3, align 4
  %vc = load i32, ptr %c, align 4
  %vd = load i32, ptr %d, align 64
  %ve = load i32, ptr %e, align 32
  %vf = load i32, ptr %f, align 4
  %s1 = add i32 %va, %vb
  %s2 = add i32 %s1, %vc
  %s3 = add i32 %s2, %vd
  %s4 = add i32 %s3, %ve
  %s5 = add i32 %s4, %vf
  call void @_ZdlPv(ptr %a)
  call void @_ZdaPv(ptr %b)
  call void @_ZdlPvRKSt9nothrow_t(ptr %c, ptr @_ZSt7nothrow)
  call void @_ZdlPvSt11align_val_t(ptr %d, i64 64)
  call void @_ZdaPvmSt11align_val_t(ptr %e, i64 32, i64 32)
  call void @_ZdlPvm(ptr %f, i64 8)
  call void @_ZdlPv(ptr null)
  %ok = icmp eq i32 %s5, 21
  call void @verifier.assume.not(i1 %ok)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
