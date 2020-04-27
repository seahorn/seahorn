; RUN: %seabmc_fatptr  "%s" 2>&1 | %oc %s

; CHECK: ^sat$
; ModuleID = 'fat_ptr_simple_sat.ll'
source_filename = "fat_ptr_outofbounds_simple_02.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@main.a = private unnamed_addr constant [3 x i8] c"aa\00", align 1, !sea.dsa.allocsite !0
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
  %sm2 = call i32 @shadow.mem.arg.init(i32 0, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm3 = call i32 @shadow.mem.init(i32 1, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm4 = call i32 @shadow.mem.init(i32 2, i8* null), !shadow.mem !4, !shadow.mem.def !4
  %sm = call i32 @shadow.mem.global.init(i32 0, i32 %sm2, i8* getelementptr inbounds ([3 x i8], [3 x i8]* @main.a, i32 0, i32 0)), !shadow.mem !4, !shadow.mem.def !0
  call void @shadow.mem.load(i32 1, i32 %sm3, i8* null), !shadow.mem !4, !shadow.mem.use !0
  %raw_ptr.i = alloca [3 x i8], align 1, !sea.dsa.allocsite !0
  %0 = bitcast [3 x i8]* %raw_ptr.i to i8*
  call void @llvm.lifetime.start.p0i8(i64 3, i8* %0)
  call void @seahorn.fn.enter() #3
  %1 = getelementptr inbounds [3 x i8], [3 x i8]* %raw_ptr.i, i64 0, i64 0
%2 = ptrtoint [3 x i8]* %raw_ptr.i to i64
  %3 = call i8* @__sea_set_extptr_slot0_hm(i8* %1, i64 %2) #3
  %4 = call i8* @__sea_set_extptr_slot1_hm(i8* %3, i64 3) #3
  call void @llvm.lifetime.start.p0i8(i64 3, i8* %4) #3
  %5 = getelementptr inbounds [3 x i8], [3 x i8]* @main.a, i64 0, i64 0
  call void @shadow.mem.trsfr.load(i32 0, i32 %sm, i8* null), !shadow.mem !4, !shadow.mem.use !0
  %sm1 = call i32 @shadow.mem.store(i32 2, i32 %sm4, i8* null), !shadow.mem !4, !shadow.mem.def !0
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* %4, i8* %5, i64 3, i32 4, i1 false) #3
  %raw_ptr1.i = getelementptr inbounds i8, i8* %4, i64 3
  %6 = call i8* @__sea_copy_extptr_slots_hm(i8* %raw_ptr1.i, i8* %4) #3
  %7 = call i64 @__sea_get_extptr_slot0_hm(i8* %6) #3
  %8 = call i64 @__sea_get_extptr_slot1_hm(i8* %6) #3
  %9 = call i8* @__sea_recover_pointer_hm(i8* %6) #3
  %10 = ptrtoint i8* %9 to i64
  %11 = icmp ugt i64 %7, %10
  %12 = add i64 %10, 1
  %13 = add i64 %7, %8
  %14 = icmp ult i64 %13, %12
  %15 = or i1 %11, %14
  call void @verifier.assume(i1 %15)
  br label %bound_overflow.i

bound_overflow.i:                                 ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %bound_overflow.i
  call void @seahorn.fail()
  br label %verifier.error.split

verifier.error.split:                             ; preds = %verifier.error
  call void @shadow.mem.in(i32 0, i32 %sm2, i32 0, i8* null), !shadow.mem !4, !shadow.mem.def !4
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

attributes #0 = { argmemonly nounwind }
attributes #1 = { noreturn }
attributes #2 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind }

!llvm.module.flags = !{!2}
!llvm.ident = !{!3}

!0 = !{i64 3}
!1 = !{i64 96}
!2 = !{i32 1, !"wchar_size", i32 4}
!3 = !{!"clang version 6.0.0-1ubuntu2 (tags/RELEASE_600/final)"}
!4 = !{}
