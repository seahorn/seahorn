    ; RUN: %seabmc_fatptr  "%s" 2>&1 | %oc %s
; RUN: %seabmc_fatptr  "%s" 2>&1 | %oc %s

; CHECK: ^unsat$
; ModuleID = 'fat_ptr_store_load_unsat.ll'
source_filename = "/tmp/fat_ptr_outofbounds.01.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

declare void @verifier.assume(i1)
declare void @verifier.assume.not(i1)
declare void @seahorn.fail()
declare void @sea_dsa_alias(i8*, i8*)
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
  call void @sea_dsa_alias(i8* %4, i8* %2) #3
  %5 = call i8* @__sea_set_extptr_slot1_hm(i8* %4, i64 6)
  call void @sea_dsa_alias(i8* %4, i8* %5) #3
  %6 = call i8* @__sea_recover_pointer_hm(i8* %5)  ; data
  call void @sea_dsa_alias(i8* %6, i8* %5) #3
  %7 = bitcast i8* %6 to i8**
  %8 = alloca i8, align 1
  %9 = bitcast i8* %8 to i8**  ; address
  store i8* %6, i8** %9, align 1
  %10 = load i8*, i8** %9, align 1
  %11 = call i8* @__sea_recover_pointer_hm(i8* %10)
  call void @sea_dsa_alias(i8* %11, i8* %10) #3
  %12 = ptrtoint i8* %11 to i64
  %13 = ptrtoint i8* %6 to i64
  %14 = icmp eq i64 %12, %13
  call void @verifier.assume.not(i1 %14)
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
