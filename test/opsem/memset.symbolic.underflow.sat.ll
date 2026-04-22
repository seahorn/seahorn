; RUN: %seabmc --horn-bv2-allow-partial-word-memset "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-allow-partial-word-memset --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1)
declare void @verifier.assume(i1)
declare void @seahorn.fail()
declare i32 @nd()

define i32 @main() {
entry:
  %buf = alloca [8 x i8], align 4
  %ptr = getelementptr inbounds [8 x i8], [8 x i8]* %buf, i32 0, i32 0

  ; Keep len symbolic, but constrain it to 1 so the symbolic array path must
  ; not treat later words as fully covered after bitvector underflow.
  %len = call i32 @nd()
  %is1 = icmp eq i32 %len, 1
  call void @verifier.assume(i1 %is1)

  ; Zero the whole buffer, then memset a symbolic single byte.
  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 0, i32 8, i32 4, i1 false)
  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 12, i32 %len, i32 4, i1 false)

  ; Only byte 0 should be updated.
  %head.word.ptr = bitcast i8* %ptr to i32*
  %head.word = load i32, i32* %head.word.ptr, align 4
  %head.ok = icmp eq i32 %head.word, 12

  ; The second word is fully out of range and must remain zero.
  %tail.ptr.raw = getelementptr inbounds i8, i8* %ptr, i32 4
  %tail.word.ptr = bitcast i8* %tail.ptr.raw to i32*
  %tail.word = load i32, i32* %tail.word.ptr, align 4
  %tail.ok = icmp eq i32 %tail.word, 0

  %ok = and i1 %head.ok, %tail.ok
  call void @verifier.assume(i1 %ok)
  br label %error

error:
  call void @seahorn.fail()
  ret i32 42
}
