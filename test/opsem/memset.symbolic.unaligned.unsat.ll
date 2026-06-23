; RUN: %seabmc --horn-bv2-allow-partial-word-memset "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-allow-partial-word-memset --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: {{^unsat$}}
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1)
declare void @verifier.assume(i1)
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare i32 @nd()

define i32 @main() {
entry:
  %buf = alloca [8 x i8], align 4
  %ptr = getelementptr inbounds [8 x i8], [8 x i8]* %buf, i32 0, i32 0
  %dst = getelementptr inbounds i8, i8* %ptr, i32 1

  ; Keep len symbolic, but constrain it to 4 so this exercises the symbolic
  ; unaligned memset path without relying on concrete folding.
  %len = call i32 @nd()
  %is4 = icmp eq i32 %len, 4
  call void @verifier.assume(i1 %is4)

  ; Zero the whole buffer, then memset four bytes starting at p+1.
  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 0, i32 8, i32 4, i1 false)
  call void @llvm.memset.p0i8.i32(i8* %dst, i8 12, i32 %len, i32 1, i1 false)

  ; Byte 0 must remain untouched.
  %head = load i8, i8* %ptr, align 1
  %head.ok = icmp eq i8 %head, 0

  ; Bytes 1..4 should all be 0x0c.
  %mid.word.ptr = bitcast i8* %dst to i32*
  %mid.word = load i32, i32* %mid.word.ptr, align 1
  %mid.ok = icmp eq i32 %mid.word, 202116108

  ; Byte 5 is past the symbolic length and must stay zero.
  %tail.ptr = getelementptr inbounds i8, i8* %ptr, i32 5
  %tail = load i8, i8* %tail.ptr, align 1
  %tail.ok = icmp eq i8 %tail, 0

  %ok.0 = and i1 %head.ok, %mid.ok
  %ok = and i1 %ok.0, %tail.ok
  call void @verifier.assume.not(i1 %ok)
  br label %error

error:
  call void @seahorn.fail()
  ret i32 42
}
