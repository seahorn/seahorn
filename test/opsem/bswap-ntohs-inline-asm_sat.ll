; RUN: %seabmc "%s" 2>&1 | %oc %s
; RUN: %seabmc --horn-bv2-lambdas --log=opsem3 "%s" 2>&1 | %oc %s

; CHECK: ^sat$
; ModuleID = '../opsem2/bswap/bswap-ntohs-inline-asm_sat.c'
source_filename = "../opsem2/bswap/bswap-ntohs-inline-asm_sat.c"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

; Function Attrs: noinline nounwind optnone uwtable
define dso_local i32 @main(i32 %0, i8** %1) #0 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8**, align 8
  %6 = alloca i16, align 2
  %7 = alloca i16, align 2
  %8 = alloca i16, align 2
  %9 = alloca i16, align 2
  store i32 0, i32* %3, align 4
  store i32 %0, i32* %4, align 4
  store i8** %1, i8*** %5, align 8
  %10 = call zeroext i16 @nd_uint16_t()
  store i16 %10, i16* %6, align 2
  %11 = call zeroext i16 @nd_uint16_t()
  store i16 %11, i16* %7, align 2
  %12 = load i16, i16* %6, align 2
  %13 = zext i16 %12 to i32
  %14 = load i16, i16* %7, align 2
  %15 = zext i16 %14 to i32
  %16 = icmp eq i32 %13, %15
  call void @__VERIFIER_assume(i1 zeroext %16)
  %17 = load i16, i16* %6, align 2
  %18 = call zeroext i16 @ntohs(i16 zeroext %17) #3
  store i16 %18, i16* %8, align 2
  %19 = load i16, i16* %7, align 2
  %20 = call zeroext i16 @ntohs(i16 zeroext %19) #3
  store i16 %20, i16* %9, align 2
  %21 = load i16, i16* %8, align 2
  %22 = zext i16 %21 to i32
  %23 = load i16, i16* %9, align 2
  %24 = zext i16 %23 to i32
  %25 = icmp ne i32 %22, %24
  call void @__VERIFIER_assert(i1 zeroext %25)
  %26 = load i16, i16* %8, align 2
  %27 = zext i16 %26 to i32
  %28 = load i16, i16* %9, align 2
  %29 = zext i16 %28 to i32
  %30 = icmp ne i32 %27, %29
  br i1 %30, label %32, label %31

31:                                               ; preds = %2
  call void @__VERIFIER_error()
  br label %32

32:                                               ; preds = %31, %2
  %33 = phi i1 [ true, %2 ], [ false, %31 ]
  %34 = zext i1 %33 to i32
  ret i32 0
}

declare dso_local zeroext i16 @nd_uint16_t() #1

declare dso_local void @__VERIFIER_assume(i1 zeroext) #1

; Function Attrs: nounwind readnone
declare dso_local zeroext i16 @ntohs(i16 zeroext) #2

declare dso_local void @__VERIFIER_assert(i1 zeroext) #1

declare dso_local void @__VERIFIER_error() #1

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { nounwind readnone }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"Ubuntu clang version 10.0.1-++20201112101950+ef32c611aa2-1~exp1~20201112092551.202"}
