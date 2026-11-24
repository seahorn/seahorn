; sea-mlir engine with sea-vc replaced by a script: the engine passes
; SeaHorn's word size as --widen-memory and forwards sea-vc's BRUNCH_STAT
; lines.
; RUN: printf '#!/bin/sh\necho "BRUNCH_STAT args $*"\necho "result: sat"\nexit 0\n' > %t.sh
; RUN: chmod +x %t.sh
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-solve --horn-bmc-engine=sea-mlir --horn-sea-vc=%t.sh --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s
; CHECK: BRUNCH_STAT args {{.*}} --lower --widen-memory=8
; CHECK: {{^sat$}}
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"
declare i32 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
define i32 @main() {
entry:
  %x = call i32 @nd()
  %c = icmp ne i32 %x, 3
  call void @verifier.assume.not(i1 %c)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
