; sea-mlir export: a *.with.overflow result (here merged by a phi) is kept as
; its two fields; a use other than extractvalue, phi, select, freeze or
; insertvalue into it is one error naming that use, with no "operand has no
; definition yet" for the result or the phi. A store of the {iN, i1} is
; rejected as a store of an aggregate.
; RUN: not %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s
; CHECK-NOT: no definition yet
; CHECK: Error: sea-mlir export: loads and stores of aggregates are not supported yet at: {{.*}}store { i64, i1 } %r, ptr %p
; CHECK-NOT: no definition yet
; CHECK: Error: sea-mlir export: { i64, i1 } %r (a *.with.overflow result, kept as its value and overflow bit) is used by an instruction that cannot take it; only extractvalue, phi, select, freeze and insertvalue can at: {{.*}}%w = insertvalue { { i64, i1 }, i64 } undef, { i64, i1 } %r, 0
; CHECK-NOT: no definition yet
; CHECK-NOT: Error: sea-mlir export: { i64, i1 }
; CHECK: export failed
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i64 @nd()
declare i1 @nd.i1()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)


define i32 @main() {
entry:
  %p = alloca { i64, i1 }, align 8
  %x = call i64 @nd()
  %y = call i64 @nd()
  %c = call i1 @nd.i1()
  br i1 %c, label %a, label %b
a:
  %ra = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %x, i64 %y)
  br label %j
b:
  %rb = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %x, i64 1)
  br label %j
j:
  %r = phi { i64, i1 } [ %ra, %a ], [ %rb, %b ]
  store { i64, i1 } %r, ptr %p, align 8
  %q = getelementptr inbounds { i64, i1 }, ptr %p, i64 0, i32 1
  %o8 = load i8, ptr %q, align 8
  %o = trunc i8 %o8 to i1
  %w = insertvalue { { i64, i1 }, i64 } undef, { i64, i1 } %r, 0
  %wv = extractvalue { { i64, i1 }, i64 } %w, 0, 0
  %v = add i64 %wv, 0
  %ok1 = icmp eq i64 %v, 0
  %ok = or i1 %ok1, %o
  call void @verifier.assume.not(i1 %ok)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
