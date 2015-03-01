; ModuleID = 'kbfiltr_simpl1_true.cil.o3.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-unknown-linux-gnu"

declare i32 @__VERIFIER_nondet_int()

define i32 @main() nounwind {
entry:
  %0 = tail call i1 @ufo.nondet.2() nounwind
  %1 = tail call i1 @ufo.nondet.2() nounwind
  %2 = tail call i1 @ufo.nondet.2() nounwind
  %3 = tail call i1 @ufo.nondet.2() nounwind
  %4 = tail call i1 @ufo.nondet.2() nounwind
  %5 = tail call i32 @ufo.nondet.1() nounwind
  %6 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %7 = icmp eq i32 %6, 3
  br i1 %7, label %switch_1_3, label %__UFO__1

switch_1_3:                                       ; preds = %entry
  %8 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %Pivot13 = icmp slt i32 %8, 2
  br i1 %Pivot13, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %switch_1_3
  %Pivot = icmp slt i32 %8, 23
  br i1 %Pivot, label %LeafBlock8, label %LeafBlock10

LeafBlock10:                                      ; preds = %NodeBlock
  %SwitchLeaf11 = icmp eq i32 %8, 23
  br i1 %SwitchLeaf11, label %bb1.i23.i, label %bb1.i.i

LeafBlock8:                                       ; preds = %NodeBlock
  %SwitchLeaf9 = icmp eq i32 %8, 2
  br i1 %SwitchLeaf9, label %bb1.i5.i, label %bb1.i.i

LeafBlock:                                        ; preds = %switch_1_3
  %SwitchLeaf = icmp eq i32 %8, 0
  br i1 %SwitchLeaf, label %bb1.i48.i, label %bb1.i.i

bb1.i48.i:                                        ; preds = %LeafBlock
  %9 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %10 = icmp eq i32 %9, 0
  br i1 %10, label %__UFO__2, label %bb2.i49.i

bb2.i49.i:                                        ; preds = %bb1.i48.i
  %11 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

bb1.i23.i:                                        ; preds = %LeafBlock10
  %12 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %13 = icmp eq i32 %12, 0
  br i1 %13, label %__UFO__2, label %bb2.i24.i

bb2.i24.i:                                        ; preds = %bb1.i23.i
  %14 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

bb1.i5.i:                                         ; preds = %LeafBlock8
  %15 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %16 = icmp eq i32 %15, 0
  br i1 %16, label %__UFO__2, label %bb2.i6.i

bb2.i6.i:                                         ; preds = %bb1.i5.i
  %17 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

bb1.i.i:                                          ; preds = %LeafBlock, %LeafBlock8, %LeafBlock10
  %18 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %19 = icmp eq i32 %18, 0
  br i1 %19, label %__UFO__2, label %bb2.i.i

bb2.i.i:                                          ; preds = %bb1.i.i
  %20 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %__UFO__2

__UFO__1:                                         ; preds = %__UFO__1, %entry
  br label %__UFO__1

__UFO__2:                                         ; preds = %__UFO__2, %bb2.i.i, %bb1.i.i, %bb2.i6.i, %bb1.i5.i, %bb2.i24.i, %bb1.i23.i, %bb2.i49.i, %bb1.i48.i
  br label %__UFO__2
}

declare i32 @ufo.nondet.1()

declare i1 @ufo.nondet.2()
