; RUN: %seabmc --horn-bv2-allow-partial-word-memset "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-allow-partial-word-memset --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1)
declare void @verifier.assume(i1)
declare void @seahorn.fail()

define i32 @main() {
entry:
  %buf = alloca [8 x i8], align 4
  %ptr = getelementptr inbounds [8 x i8], [8 x i8]* %buf, i32 0, i32 0

  ; Start from a known zero buffer, then memset one byte past the base.
  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 0, i32 8, i32 4, i1 false)
  %dst = getelementptr inbounds i8, i8* %ptr, i32 1
  call void @llvm.memset.p0i8.i32(i8* %dst, i8 12, i32 4, i32 1, i1 false)

  ; The first aligned word should keep byte 0 untouched and update bytes 1..3.
  %head.word.ptr = bitcast i8* %ptr to i32*
  %head.word = load i32, i32* %head.word.ptr, align 4
  %head.ok = icmp eq i32 %head.word, 202116096

  ; The unaligned 4-byte window beginning at p+1 should read back all 0x0c.
  %mid.word.ptr = bitcast i8* %dst to i32*
  %mid.word = load i32, i32* %mid.word.ptr, align 1
  %mid.ok = icmp eq i32 %mid.word, 202116108

  ; The next aligned word should have only its lowest byte updated.
  %tail.ptr.raw = getelementptr inbounds i8, i8* %ptr, i32 4
  %tail.word.ptr = bitcast i8* %tail.ptr.raw to i32*
  %tail.word = load i32, i32* %tail.word.ptr, align 4
  %tail.ok = icmp eq i32 %tail.word, 12

  %ok.0 = and i1 %head.ok, %mid.ok
  %ok = and i1 %ok.0, %tail.ok
  call void @verifier.assume(i1 %ok)
  br label %error

error:
  call void @seahorn.fail()
  ret i32 42
}
