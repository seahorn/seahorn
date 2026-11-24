; SPDX-FileCopyrightText: 2026 The SeaHorn Authors
; SPDX-License-Identifier: Apache-2.0 WITH LLVM-exception

; sea-mlir export: a source file name with a NUL and a line feed (quote(),
; the escape of a string literal) is written with two hex digits per byte,
; \00 and \0A, in the default form and with memory SSA erased.
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.mlir
; RUN: %horn --keep-shadows=true --horn-shadow-mem-alloc-is-def --horn-bmc --horn-bv2 --horn-bmc-engine=sea-mlir --horn-sea-mlir-mem-ssa=erase --horn-sea-mlir-export-only --horn-sea-mlir-out=%t.erase.mlir %s 2>&1 | filecheck %s --check-prefix=LOG
; RUN: filecheck %s < %t.erase.mlir
; LOG: sea-mlir-export: wrote
; CHECK: loc("x"("a\00b\0Ac.c":7:3))
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare i64 @nd()
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()

define i32 @main() !dbg !6 {
entry:
  %x = call i64 @nd(), !dbg !9
  %neg = icmp slt i64 %x, -10
  call void @verifier.assume.not(i1 %neg)
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 42
}

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "t", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug)
!1 = !DIFile(filename: "a\00b\0Ac.c", directory: "")
!3 = !{i32 2, !"Debug Info Version", i32 3}
!5 = !DISubroutineType(types: !{})
!6 = distinct !DISubprogram(name: "main", scope: !1, file: !1, line: 1, type: !5, scopeLine: 1, spFlags: DISPFlagDefinition, unit: !0)
!9 = !DILocation(line: 7, column: 3, scope: !6)
