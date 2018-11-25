; ModuleID = 'pldi07.c'
source_filename = "pldi07.c"
target datalayout = "e-m:e-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.list = type { %struct.list*, i32 }

@Global = global i32 10, align 4

; Function Attrs: noinline nounwind optnone uwtable
define void @do_all(%struct.list*, void (i32*)*) #0 {
  %3 = alloca %struct.list*, align 8
  %4 = alloca void (i32*)*, align 8
  store %struct.list* %0, %struct.list** %3, align 8
  store void (i32*)* %1, void (i32*)** %4, align 8
  br label %5

; <label>:5:                                      ; preds = %12, %2
  %6 = load void (i32*)*, void (i32*)** %4, align 8
  %7 = load %struct.list*, %struct.list** %3, align 8
  %8 = getelementptr inbounds %struct.list, %struct.list* %7, i32 0, i32 1
  call void %6(i32* %8)
  %9 = load %struct.list*, %struct.list** %3, align 8
  %10 = getelementptr inbounds %struct.list, %struct.list* %9, i32 0, i32 0
  %11 = load %struct.list*, %struct.list** %10, align 8
  store %struct.list* %11, %struct.list** %3, align 8
  br label %12

; <label>:12:                                     ; preds = %5
  %13 = load %struct.list*, %struct.list** %3, align 8
  %14 = icmp ne %struct.list* %13, null
  br i1 %14, label %5, label %15

; <label>:15:                                     ; preds = %12
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define void @do_all2(%struct.list*, void (i32*)*) #0 {
  %3 = alloca %struct.list*, align 8
  %4 = alloca void (i32*)*, align 8
  store %struct.list* %0, %struct.list** %3, align 8
  store void (i32*)* %1, void (i32*)** %4, align 8
  br label %5

; <label>:5:                                      ; preds = %12, %2
  %6 = load void (i32*)*, void (i32*)** %4, align 8
  %7 = load %struct.list*, %struct.list** %3, align 8
  %8 = getelementptr inbounds %struct.list, %struct.list* %7, i32 0, i32 1
  call void %6(i32* %8)
  %9 = load %struct.list*, %struct.list** %3, align 8
  %10 = getelementptr inbounds %struct.list, %struct.list* %9, i32 0, i32 0
  %11 = load %struct.list*, %struct.list** %10, align 8
  store %struct.list* %11, %struct.list** %3, align 8
  br label %12

; <label>:12:                                     ; preds = %5
  %13 = load %struct.list*, %struct.list** %3, align 8
  %14 = icmp ne %struct.list* %13, null
  br i1 %14, label %5, label %15

; <label>:15:                                     ; preds = %12
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define void @addG(i32*) #0 {
  %2 = alloca i32*, align 8
  store i32* %0, i32** %2, align 8
  %3 = load i32, i32* @Global, align 4
  %4 = load i32*, i32** %2, align 8
  %5 = load i32, i32* %4, align 4
  %6 = add nsw i32 %5, %3
  store i32 %6, i32* %4, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define void @subG(i32*) #0 {
  %2 = alloca i32*, align 8
  store i32* %0, i32** %2, align 8
  %3 = load i32, i32* @Global, align 4
  %4 = load i32*, i32** %2, align 8
  %5 = load i32, i32* %4, align 4
  %6 = sub nsw i32 %5, %3
  store i32 %6, i32* %4, align 4
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define void @addGToList(%struct.list*) #0 {
  %2 = alloca %struct.list*, align 8
  store %struct.list* %0, %struct.list** %2, align 8
  %3 = load %struct.list*, %struct.list** %2, align 8
  call void @do_all(%struct.list* %3, void (i32*)* @addG)
  ret void
}

; Function Attrs: noinline nounwind optnone uwtable
define %struct.list* @makeList(i32) #0 {
  %2 = alloca i32, align 4
  %3 = alloca %struct.list*, align 8
  store i32 %0, i32* %2, align 4
  %4 = call i8* @malloc(i64 16)
  %5 = bitcast i8* %4 to %struct.list*
  store %struct.list* %5, %struct.list** %3, align 8
  %6 = load i32, i32* %2, align 4
  %7 = icmp ne i32 %6, 0
  br i1 %7, label %8, label %12

; <label>:8:                                      ; preds = %1
  %9 = load i32, i32* %2, align 4
  %10 = sub nsw i32 %9, 1
  %11 = call %struct.list* @makeList(i32 %10)
  br label %13

; <label>:12:                                     ; preds = %1
  br label %13

; <label>:13:                                     ; preds = %12, %8
  %14 = phi %struct.list* [ %11, %8 ], [ null, %12 ]
  %15 = load %struct.list*, %struct.list** %3, align 8
  %16 = getelementptr inbounds %struct.list, %struct.list* %15, i32 0, i32 0
  store %struct.list* %14, %struct.list** %16, align 8
  %17 = load i32, i32* %2, align 4
  %18 = load %struct.list*, %struct.list** %3, align 8
  %19 = getelementptr inbounds %struct.list, %struct.list* %18, i32 0, i32 1
  store i32 %17, i32* %19, align 8
  %20 = load %struct.list*, %struct.list** %3, align 8
  ret %struct.list* %20
}

declare i8* @malloc(i64) #1

; Function Attrs: noinline nounwind optnone uwtable
define i32 @main() #0 {
  %1 = alloca %struct.list*, align 8
  %2 = alloca %struct.list*, align 8
  %3 = call %struct.list* @makeList(i32 10)
  store %struct.list* %3, %struct.list** %1, align 8
  %4 = call %struct.list* @makeList(i32 100)
  store %struct.list* %4, %struct.list** %2, align 8
  %5 = load %struct.list*, %struct.list** %1, align 8
  call void @addGToList(%struct.list* %5)
  store i32 20, i32* @Global, align 4
  %6 = load %struct.list*, %struct.list** %2, align 8
  call void @addGToList(%struct.list* %6)
  %7 = load %struct.list*, %struct.list** %1, align 8
  call void @do_all2(%struct.list* %7, void (i32*)* @subG)
  ret i32 0
}

attributes #0 = { noinline nounwind optnone uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "less-precise-fpmad"="false" "no-frame-pointer-elim"="true" "no-frame-pointer-elim-non-leaf" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }

!llvm.module.flags = !{!0}
!llvm.ident = !{!1}

!0 = !{i32 1, !"wchar_size", i32 4}
!1 = !{!"clang version 6.0.0-1ubuntu2~16.04.1 (tags/RELEASE_600/final)"}
