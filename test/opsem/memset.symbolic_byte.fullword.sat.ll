; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
target datalayout = "e-m:o-p:32:32-f64:32:64-f80:128-n8:16:32-S128"
target triple = "i386-apple-macosx10.14.0"

declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i32, i1)
declare void @verifier.assume(i1)
declare void @seahorn.fail()
declare i8 @nd()

define i32 @main() {
entry:
  %buf = alloca [8 x i8], align 1
  %ptr = getelementptr inbounds [8 x i8], [8 x i8]* %buf, i32 0, i32 0

  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 0, i32 8, i32 4, i1 false)

  %byte = call i8 @nd()
  %byte_nonzero = icmp ne i8 %byte, 0
  call void @verifier.assume(i1 %byte_nonzero)
  call void @llvm.memset.p0i8.i32(i8* %ptr, i8 %byte, i32 4, i32 4, i1 false)

  %word.ptr = bitcast i8* %ptr to i32*
  %word = load i32, i32* %word.ptr, align 4

  %byte32 = zext i8 %byte to i32
  %byte.shl8 = shl i32 %byte32, 8
  %half = or i32 %byte32, %byte.shl8
  %half.shl16 = shl i32 %half, 16
  %expected = or i32 %half, %half.shl16
  %word.ok = icmp eq i32 %word, %expected

  %rest.ptr = getelementptr inbounds i8, i8* %ptr, i32 4
  %rest.word.ptr = bitcast i8* %rest.ptr to i32*
  %rest.word = load i32, i32* %rest.word.ptr, align 4
  %rest.ok = icmp eq i32 %rest.word, 0

  %ok = and i1 %word.ok, %rest.ok
  call void @verifier.assume(i1 %ok)
  br label %error

error:
  call void @seahorn.fail()
  ret i32 42
}
