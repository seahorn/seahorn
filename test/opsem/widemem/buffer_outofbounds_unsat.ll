; RUN: %seabmc --horn-bv2-ptr-size=8 --horn-bv2-word-size=8 "%s" 2>&1 | %oc %s
; CHECK: ^unsat$

; ModuleID = '/tmp/fat/bitcode.fat.pp.ms.o.ul.cut.bc'
source_filename = "fat_ptr_outofbounds.02.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@__const.main.base_a = private unnamed_addr constant [6 x i8] c"aaaaa\00", align 1
@llvm.used = appending global [8 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: nounwind uwtable
define private i32 @orig.main() local_unnamed_addr #0 {
  call void @seahorn.fn.enter() #4
  %1 = alloca [6 x i8], align 1
  %2 = getelementptr inbounds [6 x i8], [6 x i8]* %1, i64 0, i64 0
  call void @llvm.lifetime.start.p0i8(i64 6, i8* nonnull %2) #4
  %3 = getelementptr inbounds [6 x i8], [6 x i8]* %1, i64 0, i64 0
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull align 1 dereferenceable(6) %3, i8* nonnull align 1 dereferenceable(6) getelementptr inbounds ([6 x i8], [6 x i8]* @__const.main.base_a, i64 0, i64 0), i64 6, i1 false)
  %4 = getelementptr inbounds [6 x i8], [6 x i8]* %1, i64 0, i64 5
  %5 = call i1 @sea.is_dereferenceable(i8* nonnull %4, i64 1)
  br i1 %5, label %6, label %bound_overflow

6:                                                ; preds = %0
  store i8 100, i8* %4, align 1, !tbaa !2
  %7 = getelementptr inbounds [6 x i8], [6 x i8]* %1, i64 0, i64 0
  call void @llvm.lifetime.end.p0i8(i64 6, i8* nonnull %7) #4
  ret i32 0

bound_overflow:                                   ; preds = %0
  call void @verifier.error() #5
  unreachable
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i64(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i64, i1 immarg) #1

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare i1 @sea.is_dereferenceable(i8* nocapture, i64) local_unnamed_addr #2

; Function Attrs: inaccessiblememonly nofree norecurse noreturn nounwind
declare void @verifier.error() #3

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @verifier.assume(i1) #2

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @verifier.assume.not(i1) #2

; Function Attrs: inaccessiblememonly nofree norecurse nounwind
declare void @seahorn.fail() #2

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind uwtable
define dso_local i32 @main() local_unnamed_addr #0 {
entry:
  %0 = alloca [6 x i8], align 1
  call void @seahorn.fn.enter() #4
  %1 = getelementptr inbounds [6 x i8], [6 x i8]* %0, i64 0, i64 0
  call void @llvm.lifetime.start.p0i8(i64 6, i8* nonnull %1) #4
  %2 = getelementptr inbounds [6 x i8], [6 x i8]* %0, i64 0, i64 0
  call void @llvm.memcpy.p0i8.p0i8.i64(i8* nonnull align 4 dereferenceable(6) %2, i8* nonnull align 4 dereferenceable(6) getelementptr inbounds ([6 x i8], [6 x i8]* @__const.main.base_a, i64 0, i64 0), i64 6, i1 false) #4
  %3 = getelementptr inbounds [6 x i8], [6 x i8]* %0, i64 0, i64 5
  %4 = call i1 @sea.is_dereferenceable(i8* nonnull %3, i64 1) #4
  call void @verifier.assume.not(i1 %4)
  br label %bound_overflow.i

bound_overflow.i:                                 ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %bound_overflow.i
  call void @seahorn.fail()
  ret i32 42
}

declare i1 @nondet.bool()

attributes #0 = { nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="none" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind willreturn }
attributes #2 = { inaccessiblememonly nofree norecurse nounwind }
attributes #3 = { inaccessiblememonly nofree norecurse noreturn nounwind }
attributes #4 = { nounwind }
attributes #5 = { noreturn nounwind }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"Ubuntu clang version 10.0.1-++20200529022950+a634a80615b-1~exp1~20200529003547.166 "}
!2 = !{!3, !3, i64 0}
!3 = !{!"omnipotent char", !4, i64 0}
!4 = !{!"Simple C/C++ TBAA"}
