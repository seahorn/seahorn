; sea-mlir export: a phi that merges a *.with.overflow result with a
; constant {iN, i1} passes the constant's fields (zeroinitializer: zeros;
; undef: a nondet value and a nondet bit), and with a struct value (an
; insertvalue chain) its sea.struct.extract fields. An insertvalue into a
; merged result replaces one field. The property holds (sea-vc --lower:
; unsat).
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; LOG-NOT: Error
; LOG: sea-mlir-export: wrote
; CHECK: sea.program @"main"
; CHECK: %[[S:v[0-9]+]] = sea.struct.insert %{{v[0-9]+}}, %{{v[0-9]+}}[1] : i1 into !sea.struct<i64, i1>
; CHECK: %[[C7:v[0-9]+]] = sea.const 7 : i64
; CHECK: %[[T:v[0-9]+]] = sea.const 1 : i1
; CHECK: %[[Z:v[0-9]+]] = sea.const 0 : i64
; CHECK: %[[ZO:v[0-9]+]] = sea.const 0 : i1
; CHECK: %[[SV:v[0-9]+]] = sea.struct.extract %[[S]][0] : !sea.struct<i64, i1> -> i64
; CHECK: %[[SO:v[0-9]+]] = sea.struct.extract %[[S]][1] : !sea.struct<i64, i1> -> i1
; CHECK: %[[U:v[0-9]+]] = sea.nondet "undef" {{.*}} : i64
; CHECK: %[[UO:v[0-9]+]] = sea.nondet "undef" {{.*}} : i1
; CHECK: sea.br ^bb3(%[[C7]], %[[T]], %[[Z]], %[[ZO]], %[[SV]], %[[SO]], %[[U]], %[[UO]] : i64, i1, i64, i1, i64, i1, i64, i1)
; CHECK: %[[A:v[0-9]+]] = sea.add
; CHECK: %[[AO:v[0-9]+]] = sea.saddo
; CHECK: sea.br ^bb3(%[[A]], %[[AO]], %[[A]], %[[AO]], %[[A]], %[[AO]], %[[A]], %[[AO]] : i64, i1, i64, i1, i64, i1, i64, i1)
; CHECK: ^bb3(
; CHECK: sea.assert
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i64 @nd()
declare i1 @nd.i1()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare { i64, i1 } @llvm.sadd.with.overflow.i64(i64, i64)

define i32 @main() {
entry:
  %x = call i64 @nd()
  %y = call i64 @nd()
  %c = call i1 @nd.i1()
  br i1 %c, label %a, label %b
a:
  %ra = call { i64, i1 } @llvm.sadd.with.overflow.i64(i64 %x, i64 %y)
  br label %j
b:
  %s0 = insertvalue { i64, i1 } undef, i64 %x, 0
  %s1 = insertvalue { i64, i1 } %s0, i1 false, 1
  br label %j
j:
  %r = phi { i64, i1 } [ %ra, %a ], [ { i64 7, i1 true }, %b ]
  %z = phi { i64, i1 } [ %ra, %a ], [ zeroinitializer, %b ]
  %s = phi { i64, i1 } [ %ra, %a ], [ %s1, %b ]
  %u = phi { i64, i1 } [ %ra, %a ], [ undef, %b ]
  %zi = insertvalue { i64, i1 } %z, i64 5, 0
  %v = extractvalue { i64, i1 } %r, 0
  %o = extractvalue { i64, i1 } %r, 1
  %zv = extractvalue { i64, i1 } %zi, 0
  %zo = extractvalue { i64, i1 } %zi, 1
  %uv = extractvalue { i64, i1 } %u, 0
  %yy = add i64 %y, 0
  %ev = add i64 %x, %yy
  %sx = icmp slt i64 %x, 0
  %sy = icmp slt i64 %yy, 0
  %sv = icmp slt i64 %ev, 0
  %same = icmp eq i1 %sx, %sy
  %flip = icmp ne i1 %sv, %sx
  %eo = and i1 %same, %flip
  %ev1 = select i1 %c, i64 %ev, i64 7
  %eo1 = select i1 %c, i1 %eo, i1 true
  %eo2 = select i1 %c, i1 %eo, i1 false
  %okv = icmp eq i64 %v, %ev1
  %oko = icmp eq i1 %o, %eo1
  %okzv = icmp eq i64 %zv, 5
  %okzo = icmp eq i1 %zo, %eo2
  %ok1 = and i1 %okv, %oko
  %ok2 = and i1 %okzv, %okzo
  %ok3 = and i1 %ok1, %ok2
  %oku = icmp ule i64 %uv, -1
  %ok4 = and i1 %ok3, %oku
  %tv = extractvalue { i64, i1 } %s, 0
  %to = extractvalue { i64, i1 } %s, 1
  %esv = select i1 %c, i64 %ev, i64 %x
  %oksv = icmp eq i64 %tv, %esv
  %okso = icmp eq i1 %to, %eo2
  %ok5 = and i1 %oksv, %okso
  %ok = and i1 %ok4, %ok5
  call void @verifier.assume.not(i1 %ok)
  br label %verifier.error
verifier.error:
  call void @seahorn.fail()
  ret i32 42
}
