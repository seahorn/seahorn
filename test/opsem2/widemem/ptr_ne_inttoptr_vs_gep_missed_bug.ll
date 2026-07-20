; RUN: %sea "%s" --horn-bv2-widemem 2>&1 | filecheck %s
; RUN: %sea "%s" --horn-bv2-extra-widemem 2>&1 | filecheck %s
; CHECK: {{^sat$}}
;
; Companion to ptr_eq_inttoptr_vs_gep.ll, exercising the OTHER direction of the
; same ExtraWideMemManagerCore::ptrEq defect -- and the more serious one.
; Now fixed (getAddressable compare); both RUN lines report `sat` (the real
; violation of `p != q` is found).
;
; Same two pointers, both denoting address 3 by different routes:
;   start = inttoptr(3)                    -> triple (base=3, offset=0)
;   end   = getelementptr(inttoptr(4), -1) -> triple (base=4, offset=-1)
;
; Here we assert `start != end`. That assertion is FALSE -- the pointers are
; equal -- so a real violation exists and the correct verdict is `sat`.
;
;   widemem       -> sat    (correct: finds the violation)
;   extra-widemem -> unsat  (WRONG: proves a disequality that does not hold,
;                            and so MISSES a real assertion violation)
;
; That makes this defect a soundness hole, not merely an imprecision: it is not
; only that extra-widemem raises false alarms on `p == q` (the companion test),
; it also silently misses genuine bugs on `p != q`.
;
; This test also serves as the vacuity control for the companion: `sat` here
; proves the path is reachable, so the companion's `unsat` under widemem is a
; real proof rather than a vacuous one.
;
; NOTE: the exact route by which extra-widemem reaches `unsat` was not pinned
; down. LLVM canonicalises `br (icmp ne a,b), ok, err` into
; `br (icmp eq a,b), err, ok`, so this may well still go through ptrEq with
; swapped successors rather than through ptrNe. Worth confirming before relying
; on the mechanism; the wrong verdict itself is reproducible either way.
;
; Note also that ptrEq and ptrNe disagree about what pointer identity means:
;
;   ptrNe -> m_main.ptrNe(getAddressable(p1), getAddressable(p2))  // base+offset
;   ptrEq -> mk<AND>(ptrEq(base1,base2), ptrEq(off1,off2))         // componentwise
;
; If both notions meet on the same pointers, SeaHorn can derive
; !(p == q) && !(p != q) -- a contradiction, which makes paths spuriously
; infeasible and is another way real bugs get pruned away.
;
; The fix mirrors ptrNe, reusing the getAddressable helper that already exists:
;
;   return m_main.ptrEq(getAddressable(p1), getAddressable(p2));

declare i64 @nd_int()
declare void @__VERIFIER_assume(i32)
declare void @__VERIFIER_error()

define i32 @main() {
entry:
  ; nd + assume rather than literals, so the frontend cannot constant-fold
  ; gep(inttoptr(4), -1) into inttoptr(3) -- that fold is what must be avoided.
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

  ; start != end is FALSE, so this assertion must be violated -> sat.
  %ne = icmp ne ptr %start, %end
  br i1 %ne, label %ok, label %err

err:
  call void @__VERIFIER_error()
  unreachable

ok:
  ret i32 0
}
