; seapp: an available_externally function (as libstdc++'s extern-template
; members, e.g. std::basic_string<char>) has a body, but InternalizePass keeps
; its linkage, so --horn-inline-all does not inline it, and the sea-mlir
; export fails on the call. --seapp-define-available-externally gives it
; linkonce_odr linkage first; sea turns the option on for
; --horn-bmc-engine=sea-mlir. noinline stands for a body too large for the
; -O3 inliner, which would otherwise inline it later.
; RUN: rm -f %t.old.ll %t.new.ll %t.mlir.ll %t.mlir %t.off.mlir
; RUN: %sea pp -S %s -o %t.old.ll
; RUN: filecheck %s --check-prefix=OLD < %t.old.ll
; RUN: %sea pp -S --seapp-define-available-externally %s -o %t.new.ll
; RUN: filecheck %s --check-prefix=NEW < %t.new.ll
; RUN: %sea pp -S --horn-bmc-engine=sea-mlir %s -o %t.mlir.ll
; RUN: filecheck %s --check-prefix=NEW < %t.mlir.ll
; RUN: %sea yama -y sea-mlir-export --bound=1 -m64 --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; RUN: not %sea yama -y sea-mlir-export --bound=1 -m64 --seapp-define-available-externally=false --horn-sea-mlir-out=%t.off.mlir %s 2>&1 | filecheck %s --check-prefix=OFF
; OLD: define available_externally i32 @_Z4incrPi(
; NEW: define internal {{.*}}i32 @_Z4incrPi(
; LOG-NOT: Error
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK-NOT: _Z4incrPi
; CHECK: sea.assert
; OFF: Error: sea-mlir export: call to _Z4incrPi was not inlined
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i32 @nd()
declare void @__VERIFIER_error()

define available_externally i32 @_Z4incrPi(ptr %p) #0 {
entry:
  %v = load i32, ptr %p, align 4
  %w = add nsw i32 %v, 1
  store i32 %w, ptr %p, align 4
  ret i32 %w
}

define i32 @main() {
entry:
  %x = alloca i32, align 4
  %n = call i32 @nd()
  %s = and i32 %n, 15
  store i32 %s, ptr %x, align 4
  %r = call i32 @_Z4incrPi(ptr %x)
  %c = icmp sgt i32 %r, 16
  br i1 %c, label %err, label %ok
err:
  call void @__VERIFIER_error()
  unreachable
ok:
  ret i32 0
}

attributes #0 = { noinline }
