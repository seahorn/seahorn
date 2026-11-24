; SPDX-FileCopyrightText: 2026 The SeaHorn Authors
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; An indirect Boolean predicate used as an assume condition has no direct
; Function. Promoting the assume must preserve the predicate, not dereference
; a null callee while looking for a partial-function annotation.
; RUN: %sea pp -S %s -o %t.ll
; RUN: filecheck %s < %t.ll
; CHECK-LABEL: define i32 @main(ptr %predicate)
; CHECK: %value = call i1 %predicate()
; CHECK: call void @verifier.assume(i1 %value)

declare void @__VERIFIER_assume(i32)

define i32 @main(ptr %predicate) {
entry:
  %value = call i1 %predicate()
  %condition = zext i1 %value to i32
  call void @__VERIFIER_assume(i32 %condition)
  ret i32 0
}
