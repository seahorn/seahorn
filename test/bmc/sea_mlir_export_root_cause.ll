; sea-mlir export diagnostics: an instruction that fails to export is
; reported once, with its reason; the values computed from it are undefined,
; and one line names the root cause at their first use instead of an
; "operand has no definition yet" error per use. A call to a defined function
; that was not inlined is reported once per callee, naming the call, also
; when its shadow.mem.arg.mod / arg.new are what the export meets first.
; RUN: not %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s
; CHECK-NOT: no definition yet
; CHECK: Error: sea-mlir export: external call returning a non-integer is not supported at: {{.*}}%p = call ptr @getp()
; CHECK-NOT: no definition yet
; CHECK: Error: sea-mlir export: operand %p is undefined because `%p = call ptr @getp()` failed to export (external call returning a non-integer is not supported); later uses of the values computed from it are not reported
; CHECK-NOT: no definition yet
; CHECK-NOT: unsupported shadow memory function
; CHECK: Error: sea-mlir export: call to set was not inlined (it has shadow.mem.arg.{{mod|new}}; the exporter expects every call to a defined function inlined) at: {{.*}}call void @set(ptr @g)
; CHECK-NOT: no definition yet
; CHECK-NOT: unsupported shadow memory function
; CHECK-NOT: Error: sea-mlir export: call to set
; CHECK: Error: sea-mlir export: operand %{{sh[0-9]*}} is undefined because `call void @set(ptr @g)` failed to export (call to set was not inlined
; CHECK-NOT: no definition yet
; CHECK-NOT: unsupported shadow memory function
; CHECK-NOT: Error: sea-mlir export: call to set
; CHECK-NOT: without a shadow.mem
; CHECK: Warning: sea-mlir export: 1 more calls to the functions reported above as not inlined
; CHECK: Warning: sea-mlir export: {{[0-9]+}} more uses of values left undefined by the errors above were not reported
; CHECK: export failed
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@g = global i32 0, align 4

declare ptr @getp()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()

define void @set(ptr %q) noinline {
  store i32 7, ptr %q, align 4
  ret void
}

define i32 @main() {
entry:
  %p = call ptr @getp()
  %v = load i32, ptr %p, align 4
  %w = add i32 %v, 1
  %x = mul i32 %w, %v
  store i32 %x, ptr @g, align 4
  %z = load i32, ptr @g, align 4
  call void @set(ptr @g)
  call void @set(ptr @g)
  %y = load i32, ptr @g, align 4
  %s0 = add i32 %x, %y
  %s = add i32 %s0, %z
  %ok = icmp sgt i32 %s, 0
  call void @verifier.assume.not(i1 %ok)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
