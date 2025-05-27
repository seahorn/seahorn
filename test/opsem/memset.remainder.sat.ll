; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1)
declare void @verifier.assume(i1)
declare void @seahorn.fail()

define i32 @main() {
entry:
  %buf = alloca [8 x i8], align 1
  %ptr = getelementptr inbounds [8 x i8], [8 x i8]* %buf, i32 0, i32 0
  ; Start from a known zero buffer, then set 6 bytes so one full word and one
  ; 2-byte remainder are updated.
  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 0, i32 8, i32 4, i1 false)
  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 12, i32 6, i32 4, i1 false)

  ; The first word should be fully overwritten with 0x0c bytes.
  %word.ptr = bitcast i8* %ptr to i32*
  %word = load i32, i32* %word.ptr, align 4
  %word.ok = icmp eq i32 %word, 202116108

  ; The remainder should update only the next 2 bytes.
  %tail.ptr.raw = getelementptr inbounds i8, i8* %ptr, i32 4
  %tail.ptr = bitcast i8* %tail.ptr.raw to i16*
  %tail = load i16, i16* %tail.ptr, align 2
  %tail.ok = icmp eq i16 %tail, 3084

  ; Bytes past the memset length must stay untouched.
  %rest.ptr = getelementptr inbounds i8, i8* %ptr, i32 6
  %rest = load i8, i8* %rest.ptr, align 1
  %rest.ok = icmp eq i8 %rest, 0

  %ok.0 = and i1 %word.ok, %tail.ok
  %ok = and i1 %ok.0, %rest.ok
  call void @verifier.assume(i1 %ok)
  br label %error

error:
  call void @seahorn.fail()
  ret i32 42
}
