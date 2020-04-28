; RUN: %horn --horn-bmc --keep-shadows=true --sea-dsa=ci \
; RUN:       -horn-inter-proc -horn-sem-lvl=mem --horn-gsa=false \
; RUN:       --horn-step=large --horn-bv2=true --horn-stats \
; RUN:       --log="shadow_verbose" --log="shadow_optimizer" \
; RUN:       "%s" 2>&1 | OutputCheck %s --comment=";"

; CHECK-L: Module before shadow insertion:
; CHECK-L: ret i32 42

; CHECK-L: MemSSA optimizer: 1 use(s) solved.

; CHECK-L: Module after shadow insertion:
; CHECK-L:  %sm = call i32 @shadow.mem.store(i32 0, i32 %sm3, i8* null), !shadow.mem
; CHECK-L:  %sm1 = call i32 @shadow.mem.store(i32 0, i32 %sm, i8* null), !shadow.mem
; CHECK-L:  %sm2 = call i32 @shadow.mem.store(i32 0, i32 %sm1, i8* null), !shadow.mem
; CHECK-L:  call void @shadow.mem.load(i32 0, i32 %sm, i8* null), !shadow.mem
; CHECK-L:  ret i32 42

; ModuleID = '/tmp/sea-U0ExWZ/memssa-struct-1.pp.ms.o.ul.cut.o.bc'
source_filename = "/media/nvme/projects/seahorn-5/test/memssa/memssa-struct-1.c"
target datalayout = "e-m:e-p:32:32-f64:32:64-f80:32-n8:16:32-S128"
target triple = "i386-pc-linux-gnu"

%struct.Foo = type { i32, float, i8 }

@llvm.used = appending global [12 x i8*] [i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*), i8* bitcast (void (i1)* @verifier.assume to i8*), i8* bitcast (void (i1)* @verifier.assume.not to i8*), i8* bitcast (void ()* @verifier.error to i8*), i8* bitcast (void ()* @seahorn.fail to i8*)], section "llvm.metadata"

; Function Attrs: argmemonly nounwind
declare void @llvm.lifetime.start.p0i8(i64, i8* nocapture) #0

declare void @sea_dsa_alias(i32*, i32*) local_unnamed_addr #1

declare void @verifier.assume(i1)

declare void @verifier.assume.not(i1)

declare void @seahorn.fail()

; Function Attrs: noreturn
declare void @verifier.error() #2

declare void @seahorn.fn.enter() local_unnamed_addr

; Function Attrs: nounwind
define i32 @main() local_unnamed_addr #3 {
entry:
  %0 = alloca %struct.Foo, align 4
  %1 = alloca %struct.Foo, align 4
  call void @seahorn.fn.enter() #4
  %2 = bitcast %struct.Foo* %0 to i8*
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %2) #4
  %3 = bitcast %struct.Foo* %1 to i8*
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %3) #4
  %4 = getelementptr inbounds %struct.Foo, %struct.Foo* %0, i32 0, i32 0
  %5 = getelementptr inbounds %struct.Foo, %struct.Foo* %1, i32 0, i32 0
  call void @sea_dsa_alias(i32* %4, i32* %5) #4
  %6 = getelementptr inbounds %struct.Foo, %struct.Foo* %0, i32 0, i32 0
  store i32 42, i32* %6, align 4, !tbaa !3
  %7 = getelementptr inbounds %struct.Foo, %struct.Foo* %0, i32 0, i32 1
  store float 0x40091EB860000000, float* %7, align 4, !tbaa !9
  %8 = getelementptr inbounds %struct.Foo, %struct.Foo* %1, i32 0, i32 0
  store i32 33, i32* %8, align 4, !tbaa !3
  %9 = getelementptr inbounds %struct.Foo, %struct.Foo* %0, i32 0, i32 0
  %10 = getelementptr inbounds %struct.Foo, %struct.Foo* %1, i32 0, i32 0
  call void @sea_dsa_alias(i32* %9, i32* %10) #4
  %11 = getelementptr inbounds %struct.Foo, %struct.Foo* %0, i32 0, i32 0
  %12 = load i32, i32* %11, align 4, !tbaa !3
  %13 = icmp eq i32 %12, 42
  call void @verifier.assume.not(i1 %13)
  br label %14

; <label>:14:                                     ; preds = %entry
  br label %verifier.error

verifier.error:                                   ; preds = %14
  call void @seahorn.fail()
  ret i32 42
}

attributes #0 = { argmemonly nounwind }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { noreturn }
attributes #3 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="false" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="pentium4" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }

!llvm.module.flags = !{!0, !1}
!llvm.ident = !{!2}

!0 = !{i32 1, !"NumRegisterParameters", i32 0}
!1 = !{i32 1, !"wchar_size", i32 4}
!2 = !{!"clang version 5.0.1-4 (tags/RELEASE_501/final)"}
!3 = !{!4, !5, i64 0}
!4 = !{!"", !5, i64 0, !8, i64 4, !6, i64 8}
!5 = !{!"int", !6, i64 0}
!6 = !{!"omnipotent char", !7, i64 0}
!7 = !{!"Simple C/C++ TBAA"}
!8 = !{!"float", !6, i64 0}
!9 = !{!4, !8, i64 4}
