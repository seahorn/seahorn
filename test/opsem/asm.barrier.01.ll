; RUN: %seabmc "%s" 2>&1 | %oc %s --check-prefix=OLD
; RUN: %seabmc --horn-bv2-asm-barrier "%s" 2>&1 | %oc %s --check-prefix=NEW

; BvOpSem2: a comment-only asm with a memory clobber (Firedancer's
; FD_COMPILER_MFENCE) has no effect either way. By default (dev18 behavior)
; it is reported as unsupported; with --horn-bv2-asm-barrier it is accepted
; silently as a compiler barrier.
; OLD: Cannot handle inline assembly
; OLD: {{^unsat$}}
; NEW-NOT: Cannot handle inline assembly
; NEW: {{^unsat$}}
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

@g = global i32 0, align 4

declare i32 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()

define i32 @main() {
entry:
  %x = call i32 @nd()
  store i32 %x, ptr @g, align 4
  call void asm sideeffect "# FD_COMPILER_MFENCE()", "~{memory},~{dirflag},~{fpsr},~{flags}"()
  %v = load i32, ptr @g, align 4
  %c = icmp eq i32 %v, %x
  call void @verifier.assume.not(i1 %c)
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
