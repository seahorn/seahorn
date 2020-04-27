; RUN: %seabmc_fatptr  "%s" 2>&1 | %oc %s

; CHECK: ^unsat$
; ModuleID = 'fat_ptr_get_set_test_unsat.ll'

source_filename = "/tmp/fat_ptr_outofbounds.01.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @verifier.assume(i1)
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare i64 @__sea_get_extptr_slot0_hm(i8*)
declare i64 @__sea_get_extptr_slot1_hm(i8*)
declare i8* @__sea_set_extptr_slot0_hm(i8*, i64)
declare i8* @__sea_set_extptr_slot1_hm(i8*, i64)
declare i8* @__sea_copy_extptr_slots_hm(i8*, i8*)
declare i8* @__sea_recover_pointer_hm(i8*)

; Function Attrs: nounwind uwtable
define i32 @main() #0 {
  %1 = alloca i8, align 1
  %2 = bitcast i8* %1 to i8*
  %3 = ptrtoint i8* %1 to i64
  %4 = call i8* @__sea_set_extptr_slot0_hm(i8* %2, i64 %3)
  %5 = call i8* @__sea_set_extptr_slot1_hm(i8* %4, i64 6)
  %6 = call i64 @__sea_get_extptr_slot0_hm(i8* %4)
  %7 = call i64 @__sea_get_extptr_slot1_hm(i8* %5)
  %8 = icmp eq i64 %3, %6
  %9 = icmp eq i64 6, %7
  %10 = and i1 %8, %9  ; assert both slot0 and slot1 have expected data
  %11 = alloca i8, align 1
  %12 = call i8* @__sea_copy_extptr_slots_hm(i8* %11, i8* %5)
  %13 = call i64 @__sea_get_extptr_slot0_hm(i8* %12)
  %14 = call i64 @__sea_get_extptr_slot1_hm(i8* %12)
  %15 = icmp eq i64 %3, %13
  %16 = icmp eq i64 6, %14
  %17 = and i1 %15, %16
  %18 = and i1 %17, %10  ; assert copy behaves as expected and previous assert is true
  %19 = call i8* @__sea_recover_pointer_hm(i8* %12)
  %20 = ptrtoint i8* %12 to i64
  %21 = ptrtoint i8* %19 to i64
  %22 = icmp eq i64 %21, %20
  %23 = and i1 %22, %18  ; assert recover behaves as expected and previous assert is true
  call void @verifier.assume.not(i1 %23)
  br label %verifier.error

verifier.error:
  call void @seahorn.fail()
  ret i32 1
}

attributes #0 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind }
attributes #2 = { noreturn }
attributes #3 = { nounwind }
attributes #4 = { noreturn nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
!2 = !{!3, !4, i64 0}
!3 = !{!"bounded_array", !4, i64 0, !7, i64 8}
!4 = !{!"any pointer", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = !{!"long", !5, i64 0}
!8 = !{!3, !7, i64 8}
!9 = !{!5, !5, i64 0}
