; ModuleID = 'kbfiltr_simpl2_true.cil.o3.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-unknown-linux-gnu"

declare i32 @__VERIFIER_nondet_int()

define i32 @main() nounwind {
entry:
  %0 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %1 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %2 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %3 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %4 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %5 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %6 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %7 = tail call i32 @ufo.nondet.2() nounwind
  %8 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %9 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %10 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %11 = icmp eq i32 %10, 0
  %12 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %11, label %switch_1_0, label %bb4

bb4:                                              ; preds = %entry
  %13 = icmp eq i32 %12, 1
  %14 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %13, label %switch_1_1, label %bb5

bb5:                                              ; preds = %bb4
  %15 = icmp eq i32 %14, 3
  %16 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %15, label %NodeBlock16, label %bb6

bb6:                                              ; preds = %bb5
  %17 = icmp eq i32 %16, 4
  %18 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %17, label %switch_1_4, label %bb7

bb7:                                              ; preds = %bb6
  %19 = icmp eq i32 %18, 8
  br i1 %19, label %switch_1_8, label %__UFO__1

switch_1_0:                                       ; preds = %entry
  %20 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %21 = icmp eq i32 %20, 0
  br i1 %21, label %__UFO__2, label %bb3.i.i.i50

bb3.i.i.i50:                                      ; preds = %switch_1_0
  %22 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

switch_1_1:                                       ; preds = %bb4
  %23 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %24 = icmp eq i32 %23, 0
  br i1 %24, label %__UFO__2, label %bb3.i.i.i26

bb3.i.i.i26:                                      ; preds = %switch_1_1
  %25 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

NodeBlock16:                                      ; preds = %bb5
  %Pivot17 = icmp slt i32 %16, 2
  br i1 %Pivot17, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock16
  %Pivot = icmp slt i32 %16, 23
  br i1 %Pivot, label %LeafBlock12, label %LeafBlock14

LeafBlock14:                                      ; preds = %NodeBlock
  %SwitchLeaf15 = icmp eq i32 %16, 23
  br i1 %SwitchLeaf15, label %bb2.i23.i, label %bb2.i.i8

LeafBlock12:                                      ; preds = %NodeBlock
  %SwitchLeaf13 = icmp eq i32 %16, 2
  br i1 %SwitchLeaf13, label %bb2.i5.i, label %bb2.i.i8

LeafBlock:                                        ; preds = %NodeBlock16
  %SwitchLeaf = icmp eq i32 %16, 0
  br i1 %SwitchLeaf, label %bb2.i48.i, label %bb2.i.i8

bb2.i48.i:                                        ; preds = %LeafBlock
  %26 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %27 = icmp eq i32 %26, 0
  br i1 %27, label %__UFO__2, label %bb3.i49.i

bb3.i49.i:                                        ; preds = %bb2.i48.i
  %28 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

bb2.i23.i:                                        ; preds = %LeafBlock14
  %29 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %30 = icmp eq i32 %29, 0
  br i1 %30, label %__UFO__2, label %bb3.i24.i

bb3.i24.i:                                        ; preds = %bb2.i23.i
  %31 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

bb2.i5.i:                                         ; preds = %LeafBlock12
  %32 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %33 = icmp eq i32 %32, 0
  br i1 %33, label %__UFO__2, label %bb3.i6.i

bb3.i6.i:                                         ; preds = %bb2.i5.i
  %34 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

bb2.i.i8:                                         ; preds = %LeafBlock, %LeafBlock12, %LeafBlock14
  %35 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %36 = icmp eq i32 %35, 0
  br i1 %36, label %__UFO__2, label %bb3.i.i9

bb3.i.i9:                                         ; preds = %bb2.i.i8
  %37 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

switch_1_4:                                       ; preds = %bb6
  %38 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %39 = icmp eq i32 %38, 0
  br i1 %39, label %__UFO__2, label %bb3.i.i

bb3.i.i:                                          ; preds = %switch_1_4
  %40 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

switch_1_8:                                       ; preds = %bb7
  %41 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %42 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %43 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %44 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %45 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %46 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %47 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %48 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %49 = icmp eq i32 %41, %46
  br i1 %49, label %switch_7_exp_0.i, label %bb.i

bb.i:                                             ; preds = %switch_1_8
  %50 = icmp eq i32 %41, %47
  br i1 %50, label %__UFO__2, label %bb1.i

bb1.i:                                            ; preds = %bb.i
  %51 = icmp eq i32 %41, %48
  %52 = icmp slt i32 %43, %45
  %or.cond4 = and i1 %51, %52
  br i1 %or.cond4, label %__UFO__2, label %bb2.i.i.i

switch_7_exp_0.i:                                 ; preds = %switch_1_8
  %.not = icmp ne i32 %42, 0
  %53 = icmp slt i32 %43, %44
  %or.cond = or i1 %53, %.not
  br i1 %or.cond, label %__UFO__2, label %bb2.i.i.i

bb2.i.i.i:                                        ; preds = %switch_7_exp_0.i, %bb1.i
  %54 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %55 = icmp eq i32 %54, 0
  br i1 %55, label %__UFO__2, label %bb3.i.i.i

bb3.i.i.i:                                        ; preds = %bb2.i.i.i
  %56 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

__UFO__1:                                         ; preds = %__UFO__1, %bb7
  br label %__UFO__1

__UFO__2:                                         ; preds = %__UFO__2, %bb3.i.i.i, %bb2.i.i.i, %switch_7_exp_0.i, %bb1.i, %bb.i, %bb3.i.i, %switch_1_4, %bb3.i.i9, %bb2.i.i8, %bb3.i6.i, %bb2.i5.i, %bb3.i24.i, %bb2.i23.i, %bb3.i49.i, %bb2.i48.i, %bb3.i.i.i26, %switch_1_1, %bb3.i.i.i50, %switch_1_0
  br label %__UFO__2
}

declare i32 @ufo.nondet.1()

declare i32 @ufo.nondet.2()
