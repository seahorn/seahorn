; RUN: %seabmc_fatptr  "%s" 2>&1 | %oc %s

; CHECK: ^unsat$
; ModuleID = '/tmp/fat/bitcode.fat.pp.ms.o.ul.cut.bc'
source_filename = "fat_ptr_outofbounds.02.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.bounded_array = type { i8*, i64 }

@__const.main.base_a = private unnamed_addr constant [6 x i8] c"aaaaa\00", align 1
@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind uwtable
define private i32 @orig.main() local_unnamed_addr #0 {
  call void @seahorn.fn.enter() #5
  %1 = alloca i32, align 4
  %2 = bitcast i32* %1 to i8*
  %3 = ptrtoint i32* %1 to i64
  %4 = call i8* @__sea_set_extptr_slot0_hm(i8* nonnull %2, i64 %3)
  %5 = call i8* @__sea_set_extptr_slot1_hm(i8* %4, i64 4)
  call void @sea_dsa_alias(i8* nonnull %2, i8* %4) #5
  call void @sea_dsa_alias(i8* %4, i8* %5) #5
  %6 = alloca [6 x i8], align 1
  %7 = getelementptr inbounds [6 x i8], [6 x i8]* %6, i64 0, i64 0
  %8 = ptrtoint [6 x i8]* %6 to i64
  %9 = call i8* @__sea_set_extptr_slot0_hm(i8* nonnull %7, i64 %8)
  %10 = call i8* @__sea_set_extptr_slot1_hm(i8* %9, i64 6)
  call void @sea_dsa_alias(i8* nonnull %7, i8* %9) #5
  call void @sea_dsa_alias(i8* %9, i8* %10) #5
  %11 = alloca %struct.bounded_array, align 8
  %12 = bitcast %struct.bounded_array* %11 to i8*
  %13 = ptrtoint %struct.bounded_array* %11 to i64
  %14 = call i8* @__sea_set_extptr_slot0_hm(i8* nonnull %12, i64 %13)
  %15 = call i8* @__sea_set_extptr_slot1_hm(i8* %14, i64 16)
  call void @sea_dsa_alias(i8* nonnull %12, i8* %14) #5
  call void @sea_dsa_alias(i8* %14, i8* %15) #5
  %16 = call i8* @__sea_recover_pointer_hm(i8* %5)
  call void @sea_dsa_alias(i8* %5, i8* %16) #5
  %17 = call i64 @__sea_get_extptr_slot0_hm(i8* %5)
  %18 = call i64 @__sea_get_extptr_slot1_hm(i8* %5)
  %19 = ptrtoint i8* %16 to i64
  %20 = icmp ugt i64 %17, %19
  %21 = add i64 %19, 4
  %22 = add i64 %17, %18
  %23 = icmp ult i64 %22, %21
  %24 = or i1 %20, %23
  br i1 %24, label %bound_overflow, label %25

25:                                               ; preds = %0
  %26 = bitcast i8* %16 to i32*
  store i32 0, i32* %26, align 4
  call void @llvm.lifetime.start.p0i8(i64 6, i8* %10) #5
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull align 1 dereferenceable(6) %10, i8* nonnull align 1 dereferenceable(6) getelementptr inbounds ([6 x i8], [6 x i8]* @__const.main.base_a, i64 0, i64 0), i64 6, i1 false)
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %15) #5
  %27 = call i8* @__sea_recover_pointer_hm(i8* %15)
  call void @sea_dsa_alias(i8* %15, i8* %27) #5
  %28 = call i8* @__sea_copy_extptr_slots_hm(i8* %27, i8* %15)
  call void @sea_dsa_alias(i8* %27, i8* %28) #5
  %29 = call i8* @__sea_recover_pointer_hm(i8* %10)
  call void @sea_dsa_alias(i8* %10, i8* %29) #5
  %30 = call i8* @__sea_copy_extptr_slots_hm(i8* %29, i8* %10)
  call void @sea_dsa_alias(i8* %29, i8* %30) #5
  %31 = call i8* @__sea_recover_pointer_hm(i8* %28)
  call void @sea_dsa_alias(i8* %28, i8* %31) #5
  %32 = call i64 @__sea_get_extptr_slot0_hm(i8* %28)
  %33 = call i64 @__sea_get_extptr_slot1_hm(i8* %28)
  %34 = ptrtoint i8* %31 to i64
  %35 = icmp ugt i64 %32, %34
  %36 = add i64 %34, 8
  %37 = add i64 %32, %33
  %38 = icmp ult i64 %37, %36
  %39 = or i1 %35, %38
  br i1 %39, label %bound_overflow, label %40

40:                                               ; preds = %25
  %41 = bitcast i8* %31 to i8**
  store i8* %30, i8** %41, align 8, !tbaa !2
  %42 = call i8* @__sea_recover_pointer_hm(i8* %15)
  call void @sea_dsa_alias(i8* %15, i8* %42) #5
  %43 = getelementptr inbounds i8, i8* %42, i64 8
  %44 = call i8* @__sea_copy_extptr_slots_hm(i8* nonnull %43, i8* %15)
  call void @sea_dsa_alias(i8* nonnull %43, i8* %44) #5
  %45 = call i8* @__sea_recover_pointer_hm(i8* %44)
  call void @sea_dsa_alias(i8* %44, i8* %45) #5
  %46 = call i64 @__sea_get_extptr_slot0_hm(i8* %44)
  %47 = call i64 @__sea_get_extptr_slot1_hm(i8* %44)
  %48 = ptrtoint i8* %45 to i64
  %49 = icmp ugt i64 %46, %48
  %50 = add i64 %48, 8
  %51 = add i64 %46, %47
  %52 = icmp ult i64 %51, %50
  %53 = or i1 %49, %52
  br i1 %53, label %bound_overflow, label %54

54:                                               ; preds = %40
  %55 = bitcast i8* %45 to i64*
  store i64 6, i64* %55, align 8, !tbaa !8
  %56 = call i8* @__sea_recover_pointer_hm(i8* %15)
  call void @sea_dsa_alias(i8* %15, i8* %56) #5
  %57 = call i8* @__sea_copy_extptr_slots_hm(i8* %56, i8* %15)
  call void @sea_dsa_alias(i8* %56, i8* %57) #5
  %58 = call i8* @__sea_recover_pointer_hm(i8* %57)
  call void @sea_dsa_alias(i8* %57, i8* %58) #5
  %59 = call i64 @__sea_get_extptr_slot0_hm(i8* %57)
  %60 = call i64 @__sea_get_extptr_slot1_hm(i8* %57)
  %61 = ptrtoint i8* %58 to i64
  %62 = icmp ugt i64 %59, %61
  %63 = add i64 %61, 8
  %64 = add i64 %59, %60
  %65 = icmp ult i64 %64, %63
  %66 = or i1 %62, %65
  br i1 %66, label %bound_overflow, label %67

67:                                               ; preds = %54
  %68 = bitcast i8* %58 to i8**
  %69 = load i8*, i8** %68, align 8, !tbaa !2
  %70 = call i8* @__sea_recover_pointer_hm(i8* %15)
  call void @sea_dsa_alias(i8* %15, i8* %70) #5
  %71 = getelementptr inbounds i8, i8* %70, i64 8
  %72 = call i8* @__sea_copy_extptr_slots_hm(i8* nonnull %71, i8* %15)
  call void @sea_dsa_alias(i8* nonnull %71, i8* %72) #5
  %73 = call i8* @__sea_recover_pointer_hm(i8* %72)
  call void @sea_dsa_alias(i8* %72, i8* %73) #5
  %74 = call i64 @__sea_get_extptr_slot0_hm(i8* %72)
  %75 = call i64 @__sea_get_extptr_slot1_hm(i8* %72)
  %76 = ptrtoint i8* %73 to i64
  %77 = icmp ugt i64 %74, %76
  %78 = add i64 %76, 8
  %79 = add i64 %74, %75
  %80 = icmp ult i64 %79, %78
  %81 = or i1 %77, %80
  br i1 %81, label %bound_overflow, label %82

82:                                               ; preds = %67
  %83 = bitcast i8* %73 to i64*
  %84 = load i64, i64* %83, align 8, !tbaa !8
  %85 = add i64 %84, -1
  %86 = call i8* @__sea_recover_pointer_hm(i8* %69)
  call void @sea_dsa_alias(i8* %69, i8* %86) #5
  %87 = getelementptr inbounds i8, i8* %86, i64 %85
  %88 = call i8* @__sea_copy_extptr_slots_hm(i8* %87, i8* %69)
  call void @sea_dsa_alias(i8* %87, i8* %88) #5
  %89 = call i8* @__sea_recover_pointer_hm(i8* %88)
  call void @sea_dsa_alias(i8* %88, i8* %89) #5
  %90 = call i64 @__sea_get_extptr_slot0_hm(i8* %88)
  %91 = call i64 @__sea_get_extptr_slot1_hm(i8* %88)
  %92 = ptrtoint i8* %89 to i64
  %93 = icmp ugt i64 %90, %92
  %94 = add i64 %92, 1
  %95 = add i64 %90, %91
  %96 = icmp ult i64 %95, %94
  %97 = or i1 %93, %96
  br i1 %97, label %bound_overflow, label %98

98:                                               ; preds = %82
  store i8 100, i8* %89, align 1, !tbaa !9
  call void @llvm.lifetime.end.p0i8(i64 16, i8* %15) #5
  call void @llvm.lifetime.end.p0i8(i64 6, i8* %10) #5
  ret i32 0

bound_overflow:                                   ; preds = %82, %67, %54, %40, %25, %0
  call void @verifier.error()
  unreachable
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #1

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: nounwind writeonly
declare i64 @__sea_get_extptr_slot0_hm(i8* nocapture) local_unnamed_addr #2

; Function Attrs: nounwind writeonly
declare i64 @__sea_get_extptr_slot1_hm(i8* nocapture) local_unnamed_addr #2

; Function Attrs: nounwind writeonly
declare i8* @__sea_set_extptr_slot0_hm(i8*, i64) local_unnamed_addr #2

; Function Attrs: nounwind writeonly
declare i8* @__sea_set_extptr_slot1_hm(i8*, i64) local_unnamed_addr #2

; Function Attrs: nounwind writeonly
declare i8* @__sea_copy_extptr_slots_hm(i8*, i8* nocapture) local_unnamed_addr #2

; Function Attrs: nounwind writeonly
declare i8* @__sea_recover_pointer_hm(i8*) local_unnamed_addr #2

declare void @sea_dsa_alias(i8*, i8*) local_unnamed_addr

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @verifier.assume(i1) #3

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @verifier.assume.not(i1) #3

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @seahorn.fail() #3

; Function Attrs: inaccessiblememonly nofree norecurse noreturn nounwind
declare void @verifier.error() #4

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #0 {
entry:
  %0 = alloca i32, align 4
  %1 = alloca [6 x i8], align 1
  %2 = alloca %struct.bounded_array, align 8
  %3 = bitcast i32* %0 to i8*
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %3)
  %4 = bitcast [6 x i8]* %1 to i8*
  call void @llvm.lifetime.start.p0i8(i64 6, i8* %4)
  %5 = bitcast %struct.bounded_array* %2 to i8*
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %5)
  call void @seahorn.fn.enter() #5
  %6 = bitcast i32* %0 to i8*
  %7 = ptrtoint i32* %0 to i64
  %8 = call i8* @__sea_set_extptr_slot0_hm(i8* nonnull %6, i64 %7) #5
  %9 = call i8* @__sea_set_extptr_slot1_hm(i8* %8, i64 4) #5
  call void @sea_dsa_alias(i8* nonnull %6, i8* %8) #5
  call void @sea_dsa_alias(i8* %8, i8* %9) #5
  %10 = getelementptr inbounds [6 x i8], [6 x i8]* %1, i64 0, i64 0
  %11 = ptrtoint [6 x i8]* %1 to i64
  %12 = call i8* @__sea_set_extptr_slot0_hm(i8* nonnull %10, i64 %11) #5
  %13 = call i8* @__sea_set_extptr_slot1_hm(i8* %12, i64 6) #5
  call void @sea_dsa_alias(i8* nonnull %10, i8* %12) #5
  call void @sea_dsa_alias(i8* %12, i8* %13) #5
  %14 = bitcast %struct.bounded_array* %2 to i8*
  %15 = ptrtoint %struct.bounded_array* %2 to i64
  %16 = call i8* @__sea_set_extptr_slot0_hm(i8* nonnull %14, i64 %15) #5
  %17 = call i8* @__sea_set_extptr_slot1_hm(i8* %16, i64 16) #5
  call void @sea_dsa_alias(i8* nonnull %14, i8* %16) #5
  call void @sea_dsa_alias(i8* %16, i8* %17) #5
  %18 = call i8* @__sea_recover_pointer_hm(i8* %9) #5
  call void @sea_dsa_alias(i8* %9, i8* %18) #5
  %19 = call i64 @__sea_get_extptr_slot0_hm(i8* %9) #5
  %20 = call i64 @__sea_get_extptr_slot1_hm(i8* %9) #5
  %21 = ptrtoint i8* %18 to i64
  %22 = icmp ugt i64 %19, %21
  %23 = add i64 %21, 4
  %24 = add i64 %19, %20
  %25 = icmp ult i64 %24, %23
  %26 = or i1 %22, %25
  br i1 %26, label %bound_overflow.i, label %27

27:                                               ; preds = %entry
  %28 = bitcast i8* %18 to i32*
  store i32 0, i32* %28, align 4
  call void @llvm.lifetime.start.p0i8(i64 6, i8* %13) #5
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull align 4 dereferenceable(6) %13, i8* nonnull align 4 dereferenceable(6) getelementptr inbounds ([6 x i8], [6 x i8]* @__const.main.base_a, i64 0, i64 0), i64 6, i1 false) #5
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %17) #5
  %29 = call i8* @__sea_recover_pointer_hm(i8* %17) #5
  call void @sea_dsa_alias(i8* %17, i8* %29) #5
  %30 = call i8* @__sea_copy_extptr_slots_hm(i8* %29, i8* %17) #5
  call void @sea_dsa_alias(i8* %29, i8* %30) #5
  %31 = call i8* @__sea_recover_pointer_hm(i8* %13) #5
  call void @sea_dsa_alias(i8* %13, i8* %31) #5
  %32 = call i8* @__sea_copy_extptr_slots_hm(i8* %31, i8* %13) #5
  call void @sea_dsa_alias(i8* %31, i8* %32) #5
  %33 = call i8* @__sea_recover_pointer_hm(i8* %30) #5
  call void @sea_dsa_alias(i8* %30, i8* %33) #5
  %34 = call i64 @__sea_get_extptr_slot0_hm(i8* %30) #5
  %35 = call i64 @__sea_get_extptr_slot1_hm(i8* %30) #5
  %36 = ptrtoint i8* %33 to i64
  %37 = icmp ugt i64 %34, %36
  %38 = add i64 %36, 8
  %39 = add i64 %34, %35
  %40 = icmp ult i64 %39, %38
  %41 = or i1 %37, %40
  br i1 %41, label %bound_overflow.i, label %42

42:                                               ; preds = %27
  %43 = bitcast i8* %33 to i8**
  store i8* %32, i8** %43, align 8, !tbaa !2
  %44 = call i8* @__sea_recover_pointer_hm(i8* %17) #5
  call void @sea_dsa_alias(i8* %17, i8* %44) #5
  %45 = getelementptr inbounds i8, i8* %44, i64 8
  %46 = call i8* @__sea_copy_extptr_slots_hm(i8* nonnull %45, i8* %17) #5
  call void @sea_dsa_alias(i8* nonnull %45, i8* %46) #5
  %47 = call i8* @__sea_recover_pointer_hm(i8* %46) #5
  call void @sea_dsa_alias(i8* %46, i8* %47) #5
  %48 = call i64 @__sea_get_extptr_slot0_hm(i8* %46) #5
  %49 = call i64 @__sea_get_extptr_slot1_hm(i8* %46) #5
  %50 = ptrtoint i8* %47 to i64
  %51 = icmp ugt i64 %48, %50
  %52 = add i64 %50, 8
  %53 = add i64 %48, %49
  %54 = icmp ult i64 %53, %52
  %55 = or i1 %51, %54
  br i1 %55, label %bound_overflow.i, label %56

56:                                               ; preds = %42
  %57 = bitcast i8* %47 to i64*
  store i64 6, i64* %57, align 8, !tbaa !8
  %58 = call i8* @__sea_recover_pointer_hm(i8* %17) #5
  call void @sea_dsa_alias(i8* %17, i8* %58) #5
  %59 = call i8* @__sea_copy_extptr_slots_hm(i8* %58, i8* %17) #5
  call void @sea_dsa_alias(i8* %58, i8* %59) #5
  %60 = call i8* @__sea_recover_pointer_hm(i8* %59) #5
  call void @sea_dsa_alias(i8* %59, i8* %60) #5
  %61 = call i64 @__sea_get_extptr_slot0_hm(i8* %59) #5
  %62 = call i64 @__sea_get_extptr_slot1_hm(i8* %59) #5
  %63 = ptrtoint i8* %60 to i64
  %64 = icmp ugt i64 %61, %63
  %65 = add i64 %63, 8
  %66 = add i64 %61, %62
  %67 = icmp ult i64 %66, %65
  %68 = or i1 %64, %67
  br i1 %68, label %bound_overflow.i, label %69

69:                                               ; preds = %56
  %70 = bitcast i8* %60 to i8**
  %71 = load i8*, i8** %70, align 8, !tbaa !2
  %72 = call i8* @__sea_recover_pointer_hm(i8* %17) #5
  call void @sea_dsa_alias(i8* %17, i8* %72) #5
  %73 = getelementptr inbounds i8, i8* %72, i64 8
  %74 = call i8* @__sea_copy_extptr_slots_hm(i8* nonnull %73, i8* %17) #5
  call void @sea_dsa_alias(i8* nonnull %73, i8* %74) #5
  %75 = call i8* @__sea_recover_pointer_hm(i8* %74) #5
  call void @sea_dsa_alias(i8* %74, i8* %75) #5
  %76 = call i64 @__sea_get_extptr_slot0_hm(i8* %74) #5
  %77 = call i64 @__sea_get_extptr_slot1_hm(i8* %74) #5
  %78 = ptrtoint i8* %75 to i64
  %79 = icmp ugt i64 %76, %78
  %80 = add i64 %78, 8
  %81 = add i64 %76, %77
  %82 = icmp ult i64 %81, %80
  %83 = or i1 %79, %82
  br i1 %83, label %bound_overflow.i, label %84

84:                                               ; preds = %69
  %85 = bitcast i8* %75 to i64*
  %86 = load i64, i64* %85, align 8, !tbaa !8
  %87 = add i64 %86, -1
  %88 = call i8* @__sea_recover_pointer_hm(i8* %71) #5
  call void @sea_dsa_alias(i8* %71, i8* %88) #5
  %89 = getelementptr inbounds i8, i8* %88, i64 %87
  %90 = call i8* @__sea_copy_extptr_slots_hm(i8* %89, i8* %71) #5
  call void @sea_dsa_alias(i8* %89, i8* %90) #5
  %91 = call i8* @__sea_recover_pointer_hm(i8* %90) #5
  call void @sea_dsa_alias(i8* %90, i8* %91) #5
  %92 = call i64 @__sea_get_extptr_slot0_hm(i8* %90) #5
  %93 = call i64 @__sea_get_extptr_slot1_hm(i8* %90) #5
  %94 = ptrtoint i8* %91 to i64
  %95 = icmp ugt i64 %92, %94
  %96 = add i64 %94, 1
  %97 = add i64 %92, %93
  %98 = icmp ult i64 %97, %96
  %99 = or i1 %95, %98
  call void @verifier.assume(i1 %99)
  br label %bound_overflow.i

bound_overflow.i:                                 ; preds = %84, %69, %56, %42, %27, %entry
  br label %verifier.error

verifier.error:                                   ; preds = %bound_overflow.i
  call void @seahorn.fail()
  ret i32 42
}

declare i1 @nondet.bool()

attributes #0 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind willreturn }
attributes #2 = { nounwind writeonly }
attributes #3 = { inaccessiblememonly nofree norecurse nounwind }
attributes #4 = { inaccessiblememonly nofree norecurse noreturn nounwind }
attributes #5 = { nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 10.0.1-++20200507062652+bab8d1790a3-1~exp1~20200507163249.158 "}
!2 = !{!3, !4, i64 0}
!3 = !{!"bounded_array", !4, i64 0, !7, i64 8}
!4 = !{!"any pointer", !5, i64 0}
!5 = !{!"omnipotent char", !6, i64 0}
!6 = !{!"Simple C/C++ TBAA"}
!7 = !{!"long", !5, i64 0}
!8 = !{!3, !7, i64 8}
!9 = !{!5, !5, i64 0}
