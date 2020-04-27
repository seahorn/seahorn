; RUN: %seabmc_fatptr  "%s" 2>&1 | %oc %s

; CHECK: ^unsat$
; ModuleID = '/tmp/fat/bitcode.fat.pp.ms.o.ul.cut.o.bc'
source_filename = "fat_ptr_outofbounds.02.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.bounded_array = type { i8*, i64 }

@main.base_a = private unnamed_addr constant [6 x i8] c"aaaaa\00", align 1, !sea.dsa.allocsite !0
@llvm.used = appending global [12 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata", !sea.dsa.allocsite !1

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #0

; Function Attrs: argmemonly nounwind
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* nocapture writeonly, i8* nocapture readonly, i64, i32, i1) #0

declare i64 @__sea_get_extptr_slot0_hm(i8*) local_unnamed_addr

declare i64 @__sea_get_extptr_slot1_hm(i8*) local_unnamed_addr

declare i8* @__sea_set_extptr_slot0_hm(i8*, i64) local_unnamed_addr

declare i8* @__sea_set_extptr_slot1_hm(i8*, i64) local_unnamed_addr

declare i8* @__sea_copy_extptr_slots_hm(i8*, i8*) local_unnamed_addr

declare i8* @__sea_recover_pointer_hm(i8*) local_unnamed_addr

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #1

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind uwtable
define i32 @main() local_unnamed_addr #2 {
entry:
  %sm4 = call i32 @shadow.mem.arg.init(i32 0, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm5 = call i32 @shadow.mem.init(i32 1, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm6 = call i32 @shadow.mem.init(i32 2, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm7 = call i32 @shadow.mem.init(i32 3, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm8 = call i32 @shadow.mem.init(i32 4, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm9 = call i32 @shadow.mem.init(i32 12, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm10 = call i32 @shadow.mem.init(i32 20, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm11 = call i32 @shadow.mem.init(i32 28, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm = call i32 @shadow.mem.global.init(i32 0, i32 %sm4, i8* getelementptr inbounds ([6 x i8], [6 x i8]* @main.base_a, i32 0, i32 0)), !shadow.mem !4, !shadow.mem.def !0
  call void @shadow.mem.load(i32 1, i32 %sm5, i8* null), !shadow.mem !4, !shadow.mem.use !0
  %raw_ptr.i = alloca [6 x i8], align 1, !sea.dsa.allocsite !0
  call void @shadow.mem.load(i32 2, i32 %sm6, i8* null), !shadow.mem !4, !shadow.mem.use !5
  %raw_ptr1.i = alloca %struct.bounded_array, align 8, !sea.dsa.allocsite !5
  %0 = bitcast [6 x i8]* %raw_ptr.i to i8*
  call void @llvm.lifetime.start.p0i8(i64 6, i8* %0)
  %1 = bitcast %struct.bounded_array* %raw_ptr1.i to i8*
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %1)
  call void @seahorn.fn.enter() #3
  %2 = getelementptr inbounds [6 x i8], [6 x i8]* %raw_ptr.i, i64 0, i64 0
  %3 = ptrtoint [6 x i8]* %raw_ptr.i to i64
  %4 = call i8* @__sea_set_extptr_slot0_hm(i8* %2, i64 %3) #3
  call void @sea_dsa_alias(i8* %4, i8* %2) #3
  %5 = call i8* @__sea_set_extptr_slot1_hm(i8* %4, i64 6) #3
  call void @sea_dsa_alias(i8* %5, i8* %4) #3
  %6 = bitcast %struct.bounded_array* %raw_ptr1.i to i8*
  %7 = ptrtoint %struct.bounded_array* %raw_ptr1.i to i64
  %8 = call i8* @__sea_set_extptr_slot0_hm(i8* %6, i64 %7) #3
  call void @sea_dsa_alias(i8* %6, i8* %8) #3
  %9 = call i8* @__sea_set_extptr_slot1_hm(i8* %8, i64 16) #3
  call void @sea_dsa_alias(i8* %8, i8* %9) #3
  call void @llvm.lifetime.start.p0i8(i64 6, i8* %5) #3
  %10 = getelementptr inbounds [6 x i8], [6 x i8]* @main.base_a, i64 0, i64 0
  call void @shadow.mem.trsfr.load(i32 0, i32 %sm, i8* null), !shadow.mem !4, !shadow.mem.use !0
  %sm1 = call i32 @shadow.mem.store(i32 3, i32 %sm7, i8* null), !shadow.mem !4, !shadow.mem.def !0
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %5, i8* %10, i64 6, i32 4, i1 false) #3
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %9) #3
  %11 = call i8* @__sea_copy_extptr_slots_hm(i8* %9, i8* %9) #3
  call void @sea_dsa_alias(i8* %9, i8* %11) #3
  %12 = call i8* @__sea_copy_extptr_slots_hm(i8* %5, i8* %5) #3
  call void @sea_dsa_alias(i8* %12, i8* %5) #3
  %13 = call i64 @__sea_get_extptr_slot0_hm(i8* %11) #3
  %14 = call i64 @__sea_get_extptr_slot1_hm(i8* %11) #3
  %15 = call i8* @__sea_recover_pointer_hm(i8* %11) #3
  call void @sea_dsa_alias(i8* %11, i8* %15) #3
  %16 = ptrtoint i8* %15 to i64
  %17 = icmp ugt i64 %13, %16
  %18 = add i64 %16, 8
  %19 = add i64 %13, %14
  %20 = icmp ult i64 %19, %18
  %21 = or i1 %17, %20
  br i1 %21, label %bound_overflow.i, label %22

; <label>:22:                                     ; preds = %entry
  %23 = bitcast i8* %15 to i8**
  %sm2 = call i32 @shadow.mem.store(i32 4, i32 %sm8, i8* null), !shadow.mem !4, !shadow.mem.def !6
  store i8* %12, i8** %23, align 8, !tbaa !7
  %raw_ptr4.i = getelementptr inbounds i8, i8* %9, i64 8
  %24 = call i8* @__sea_copy_extptr_slots_hm(i8* %raw_ptr4.i, i8* %9) #3
  call void @sea_dsa_alias(i8* %raw_ptr4.i, i8* %24) #3
  %25 = call i64 @__sea_get_extptr_slot0_hm(i8* %24) #3
  %26 = call i64 @__sea_get_extptr_slot1_hm(i8* %24) #3
  %27 = call i8* @__sea_recover_pointer_hm(i8* %24) #3
  call void @sea_dsa_alias(i8* %27, i8* %24) #3
  %28 = ptrtoint i8* %27 to i64
  %29 = icmp ugt i64 %25, %28
  %30 = add i64 %28, 8
  %31 = add i64 %25, %26
  %32 = icmp ult i64 %31, %30
  %33 = or i1 %29, %32
  br i1 %33, label %bound_overflow.i, label %34

; <label>:34:                                     ; preds = %22
  %35 = bitcast i8* %27 to i64*
  %sm3 = call i32 @shadow.mem.store(i32 12, i32 %sm9, i8* null), !shadow.mem !4, !shadow.mem.def !6
  store i64 6, i64* %35, align 8, !tbaa !13
  %36 = call i8* @__sea_copy_extptr_slots_hm(i8* %9, i8* %9) #3
  call void @sea_dsa_alias(i8* %9, i8* %36) #3
  %37 = call i64 @__sea_get_extptr_slot0_hm(i8* %36) #3
  %38 = call i64 @__sea_get_extptr_slot1_hm(i8* %36) #3
  %39 = call i8* @__sea_recover_pointer_hm(i8* %36) #3
  call void @sea_dsa_alias(i8* %36, i8* %39) #3
  %40 = ptrtoint i8* %39 to i64
  %41 = icmp ugt i64 %37, %40
  %42 = add i64 %40, 8
  %43 = add i64 %37, %38
  %44 = icmp ult i64 %43, %42
  %45 = or i1 %41, %44
  br i1 %45, label %bound_overflow.i, label %46

; <label>:46:                                     ; preds = %34
  %47 = bitcast i8* %39 to i8**
  call void @shadow.mem.load(i32 20, i32 %sm10, i8* null), !shadow.mem !4, !shadow.mem.use !6
  %48 = load i8*, i8** %47, align 8, !tbaa !7
  %raw_ptr6.i = getelementptr inbounds i8, i8* %9, i64 8
  %49 = call i8* @__sea_copy_extptr_slots_hm(i8* %raw_ptr6.i, i8* %9) #3
  call void @sea_dsa_alias(i8* %raw_ptr6.i, i8* %49) #3
  %50 = call i64 @__sea_get_extptr_slot0_hm(i8* %49) #3
  %51 = call i64 @__sea_get_extptr_slot1_hm(i8* %49) #3
  %52 = call i8* @__sea_recover_pointer_hm(i8* %49) #3
  call void @sea_dsa_alias(i8* %49, i8* %52) #3
  %53 = ptrtoint i8* %52 to i64
  %54 = icmp ugt i64 %50, %53
  %55 = add i64 %53, 8
  %56 = add i64 %50, %51
  %57 = icmp ult i64 %56, %55
  %58 = or i1 %54, %57
  br i1 %58, label %bound_overflow.i, label %59

; <label>:59:                                     ; preds = %46
  %60 = bitcast i8* %52 to i64*
  call void @shadow.mem.load(i32 28, i32 %sm11, i8* null), !shadow.mem !4, !shadow.mem.use !6
  %61 = load i64, i64* %60, align 8, !tbaa !13
  %62 = add i64 %61, -1
  %raw_ptr7.i = getelementptr inbounds i8, i8* %48, i64 %62
  %63 = call i8* @__sea_copy_extptr_slots_hm(i8* %raw_ptr7.i, i8* %48) #3
  call void @sea_dsa_alias(i8* %raw_ptr7.i, i8* %63) #3
  %64 = call i64 @__sea_get_extptr_slot0_hm(i8* %63) #3
  %65 = call i64 @__sea_get_extptr_slot1_hm(i8* %63) #3
  %66 = call i8* @__sea_recover_pointer_hm(i8* %63) #3
  call void @sea_dsa_alias(i8* %63, i8* %66) #3
  %67 = ptrtoint i8* %66 to i64
  %68 = icmp ugt i64 %64, %67
  %69 = add i64 %67, 1
  %70 = add i64 %64, %65
  %71 = icmp ult i64 %70, %69
  %72 = or i1 %68, %71
  call void @verifier.assume(i1 %72)
  br label %bound_overflow.i

bound_overflow.i:                                 ; preds = %59, %46, %34, %22, %entry
  br label %verifier.error

verifier.error:                                   ; preds = %bound_overflow.i
  call void @seahorn.fail()
  br label %verifier.error.split

verifier.error.split:                             ; preds = %verifier.error
  call void @shadow.mem.in(i32 0, i32 %sm4, i32 0, i8* null), !shadow.mem !4, !shadow.mem.def !4
  ret i32 42
}

declare void @shadow.mem.load(i32, i32, i8*)

declare void @shadow.mem.trsfr.load(i32, i32, i8*)

declare i32 @shadow.mem.store(i32, i32, i8*)

declare i32 @shadow.mem.global.init(i32, i32, i8*)

declare i32 @shadow.mem.init(i32, i8*)

declare i32 @shadow.mem.arg.init(i32, i8*)

declare void @shadow.mem.arg.ref(i32, i32, i32, i8*)

declare i32 @shadow.mem.arg.mod(i32, i32, i32, i8*)

declare i32 @shadow.mem.arg.new(i32, i32, i32, i8*)

declare void @shadow.mem.in(i32, i32, i32, i8*)

declare void @shadow.mem.out(i32, i32, i32, i8*)

declare void @sea_dsa_alias(i8*, i8*)

attributes #0 = { argmemonly nounwind }
attributes #1 = { noreturn }
attributes #2 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!2}
!llvm.ident = !{!3}

!0 = !{i64 6}
!1 = !{i64 96}
!2 = !{i32 1, !"wchar_size", i32 4}
!3 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
!4 = !{}
!5 = !{i64 16}
!6 = !{i64 8}
!7 = !{!8, !9, i64 0}
!8 = !{!"bounded_array", !9, i64 0, !12, i64 8}
!9 = !{!"any pointer", !10, i64 0}
!10 = !{!"omnipotent char", !11, i64 0}
!11 = !{!"Simple C/C++ TBAA"}
!12 = !{!"long", !10, i64 0}
!13 = !{!8, !12, i64 8}
