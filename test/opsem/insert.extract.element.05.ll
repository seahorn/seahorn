; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas "%s" 2>&1 | %oc %s

; CHECK: {{^unsat$}}
;; lane i of a bitcast vector is bits [8i, 8i+8): lane 1 is the high byte; inserting lane 0 replaces the low byte
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

declare i16 @nd()

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #0

define i32 @main() local_unnamed_addr {
entry:
  %x = call i16 @nd()
  %v = bitcast i16 %x to <2 x i8>
  %a = extractelement <2 x i8> %v, i32 1
  %hi = lshr i16 %x, 8
  %hit = trunc i16 %hi to i8
  %c1 = icmp eq i8 %a, %hit
  %w = insertelement <2 x i8> %v, i8 7, i32 0
  %b = bitcast <2 x i8> %w to i16
  %m = and i16 %x, -256
  %e = or i16 %m, 7
  %c2 = icmp eq i16 %b, %e
  %cond = and i1 %c1, %c2
  call void @verifier.assume.not(i1 %cond)
  br label %verifier.error

verifier.error:                                   ; preds = %entry
  call void @seahorn.fail()
  br label %verifier.error.split

verifier.error.split:                             ; preds = %verifier.error
  ret i32 42
}

attributes #0 = { noreturn }
