; RUN: %sea "%s" --horn-bv2-widemem 2>&1 | filecheck %s
; RUN: %sea "%s" --horn-bv2-extra-widemem 2>&1 | filecheck %s
; CHECK: {{^unsat$}}
;
; Regression test for ExtraWideMemManagerCore::ptrEq. Two pointers denoting the
; same address via different (base,offset) representations -- (4,-1) from
; `gep i8 -1` and (3,0) from inttoptr -- must compare EQUAL. The old
; componentwise ptrEq reported `sat` under --horn-bv2-extra-widemem; the fix
; (compare getAddressable(p1)==getAddressable(p2), mirroring ptrNe) makes both
; RUN lines pass. Do not "fix" this test by changing CHECK to `sat`: the
; equality holds and unsat is the correct verdict.

; Two pointers to the SAME address, reached by two different routes:
;
;   start = inttoptr(3)                 -> ExtraWide triple (base=3, offset=0)
;   end   = getelementptr(inttoptr(4), -1) -> ExtraWide triple (base=4, offset=-1)
;
; Both denote address 3, so `start == end` holds and this must be unsat.
;
; ExtraWideMemManagerCore::ptrEq compares the triple componentwise:
;
;   mk<AND>(m_main.ptrEq(p1.getBase(),   p2.getBase()),
;           m_offset.ptrEq(p1.getOffset(), p2.getOffset()))
;
; i.e. base1 == base2 && offset1 == offset2, which is strictly stronger than
; base1 + offset1 == base2 + offset2. Here it evaluates 3 == 4 && 0 == -1 ->
; false, so the equality is (wrongly) refuted and the test reports `sat`.
;
; The two triples diverge because the managers build them differently:
;   inttoptr(v) -> PtrTy(v, 0, ...)                 base is the integer, offset 0
;   ptrAdd(p,k) -> PtrTy(p.getBase(), off+k, ...)   base preserved, offset moves
;
; WideMemManager::ptrEq compares a single raw value and is unaffected, which is
; why the second RUN line passes while the first fails.
;
; This is a false alarm (imprecision), not unsoundness: SeaHorn refutes an
; equality that actually holds, reporting a bug that is not there.
;
; Found via a Rust ZST iterator (verify-rust sea-vec test_zst). A zero-sized
; type has no storage, so `start`/`end` are synthetic addresses used as counters
; and exhaustion is pointer equality. Under LLVM 18, `start += 1` keeps its
; uadd.with.overflow intrinsic (which blocks the inttoptr(ptrtoint(p)+c) -> gep
; fold) while `end -= 1` loses its intrinsic to canonicalisation and does fold to
; a gep -- so the two counters end up with different decompositions of the same
; address. Under LLVM 14 both stayed inttoptr with offset 0 and the componentwise
; comparison agreed with address comparison by luck.

declare i64 @nd_int()
declare void @__VERIFIER_assume(i32)
declare void @__VERIFIER_error()

define i32 @main() {
entry:
  ; Values come from nd_int + assume rather than literals so that the frontend
  ; cannot constant-fold gep(inttoptr(4), -1) into inttoptr(3) -- that fold is
  ; exactly what this test needs to keep apart.
  %n = call i64 @nd_int()
  %n.is4 = icmp eq i64 %n, 4
  %n.is4.i32 = zext i1 %n.is4 to i32
  call void @__VERIFIER_assume(i32 %n.is4.i32)

  %m = call i64 @nd_int()
  %m.is3 = icmp eq i64 %m, 3
  %m.is3.i32 = zext i1 %m.is3 to i32
  call void @__VERIFIER_assume(i32 %m.is3.i32)

  ; end: base 4, offset -1  (address 3)
  %end.base = inttoptr i64 %n to ptr
  %end = getelementptr i8, ptr %end.base, i64 -1

  ; start: base 3, offset 0 (address 3)
  %start = inttoptr i64 %m to ptr

  %eq = icmp eq ptr %start, %end
  br i1 %eq, label %ok, label %err

err:
  call void @__VERIFIER_error()
  unreachable

ok:
  ret i32 0
}
