; ModuleID = 'kbfiltr_simpl2_false.cil.o3.bc'
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
  %7 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %8 = tail call i32 @ufo.nondet.2() nounwind
  %9 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %10 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %11 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %12 = icmp eq i32 %11, 0
  %13 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %12, label %switch_1_0, label %bb4

bb4:                                              ; preds = %entry
  %14 = icmp eq i32 %13, 1
  %15 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %14, label %switch_1_1, label %bb5

bb5:                                              ; preds = %bb4
  %16 = icmp eq i32 %15, 3
  %17 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %16, label %NodeBlock25, label %bb6

bb6:                                              ; preds = %bb5
  %18 = icmp eq i32 %17, 4
  %19 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %18, label %switch_1_4, label %bb7

bb7:                                              ; preds = %bb6
  %20 = icmp eq i32 %19, 8
  br i1 %20, label %switch_1_8, label %__UFO__1

switch_1_0:                                       ; preds = %entry
  %21 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %22 = icmp eq i32 %21, 0
  br i1 %22, label %_L___1, label %bb3.i.i.i50

bb3.i.i.i50:                                      ; preds = %switch_1_0
  %23 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %24 = icmp eq i32 %23, 1
  br i1 %24, label %_L___1, label %switch_2_default.i.i.i51

switch_2_default.i.i.i51:                         ; preds = %bb3.i.i.i50
  br label %_L___1

switch_1_1:                                       ; preds = %bb4
  %25 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %26 = icmp eq i32 %25, 0
  br i1 %26, label %_L___1, label %bb3.i.i.i26

bb3.i.i.i26:                                      ; preds = %switch_1_1
  %27 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %28 = icmp eq i32 %27, 1
  br i1 %28, label %_L___1, label %switch_2_default.i.i.i27

switch_2_default.i.i.i27:                         ; preds = %bb3.i.i.i26
  br label %_L___1

NodeBlock25:                                      ; preds = %bb5
  %Pivot26 = icmp slt i32 %17, 2
  br i1 %Pivot26, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock25
  %Pivot = icmp slt i32 %17, 23
  br i1 %Pivot, label %LeafBlock21, label %LeafBlock23

LeafBlock23:                                      ; preds = %NodeBlock
  %SwitchLeaf24 = icmp eq i32 %17, 23
  br i1 %SwitchLeaf24, label %bb2.i23.i, label %bb2.i.i8

LeafBlock21:                                      ; preds = %NodeBlock
  %SwitchLeaf22 = icmp eq i32 %17, 2
  br i1 %SwitchLeaf22, label %bb2.i5.i, label %bb2.i.i8

LeafBlock:                                        ; preds = %NodeBlock25
  %SwitchLeaf = icmp eq i32 %17, 0
  br i1 %SwitchLeaf, label %bb2.i48.i, label %bb2.i.i8

bb2.i48.i:                                        ; preds = %LeafBlock
  %29 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %30 = icmp eq i32 %29, 0
  br i1 %30, label %bb27.i, label %bb3.i49.i

bb3.i49.i:                                        ; preds = %bb2.i48.i
  %31 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %32 = icmp eq i32 %31, 1
  br i1 %32, label %bb27.i, label %_L___1

bb27.i:                                           ; preds = %bb3.i49.i, %bb2.i48.i
  %returnVal2.0.i51.i.reg2mem.1 = phi i32 [ 0, %bb2.i48.i ], [ -1073741823, %bb3.i49.i ]
  br label %_L___1

bb2.i23.i:                                        ; preds = %LeafBlock23
  %33 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %34 = icmp eq i32 %33, 0
  br i1 %34, label %_L___1, label %bb3.i24.i

bb3.i24.i:                                        ; preds = %bb2.i23.i
  %35 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %36 = icmp eq i32 %35, 1
  br i1 %36, label %_L___1, label %switch_2_default.i25.i

switch_2_default.i25.i:                           ; preds = %bb3.i24.i
  br label %_L___1

bb2.i5.i:                                         ; preds = %LeafBlock21
  %37 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %38 = icmp eq i32 %37, 0
  br i1 %38, label %_L___1, label %bb3.i6.i

bb3.i6.i:                                         ; preds = %bb2.i5.i
  %39 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %40 = icmp eq i32 %39, 1
  br i1 %40, label %_L___1, label %switch_2_default.i7.i

switch_2_default.i7.i:                            ; preds = %bb3.i6.i
  br label %_L___1

bb2.i.i8:                                         ; preds = %LeafBlock, %LeafBlock21, %LeafBlock23
  %41 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %42 = icmp eq i32 %41, 0
  br i1 %42, label %_L___1, label %bb3.i.i9

bb3.i.i9:                                         ; preds = %bb2.i.i8
  %43 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %44 = icmp eq i32 %43, 1
  br i1 %44, label %_L___1, label %switch_2_default.i.i

switch_2_default.i.i:                             ; preds = %bb3.i.i9
  br label %_L___1

switch_1_4:                                       ; preds = %bb6
  %45 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %46 = icmp eq i32 %45, 0
  br i1 %46, label %_L___1, label %bb3.i.i

bb3.i.i:                                          ; preds = %switch_1_4
  %47 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %48 = icmp eq i32 %47, 1
  br i1 %48, label %_L___1, label %switch_6_default.i.i

switch_6_default.i.i:                             ; preds = %bb3.i.i
  br label %_L___1

switch_1_8:                                       ; preds = %bb7
  %49 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %50 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %51 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %52 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %53 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %54 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %55 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %56 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %57 = icmp eq i32 %49, %54
  br i1 %57, label %switch_7_exp_0.i, label %bb.i

bb.i:                                             ; preds = %switch_1_8
  %58 = icmp eq i32 %49, %55
  br i1 %58, label %_L___1, label %bb1.i

bb1.i:                                            ; preds = %bb.i
  %59 = icmp eq i32 %49, %56
  %60 = icmp slt i32 %51, %53
  %or.cond18 = and i1 %59, %60
  br i1 %or.cond18, label %_L___1, label %bb2.i.i.i

switch_7_exp_0.i:                                 ; preds = %switch_1_8
  %61 = icmp eq i32 %50, 0
  br i1 %61, label %bb10.i, label %_L___1

bb10.i:                                           ; preds = %switch_7_exp_0.i
  %62 = icmp slt i32 %51, %52
  br i1 %62, label %_L___1, label %bb2.i.i.i

bb2.i.i.i:                                        ; preds = %bb10.i, %bb1.i
  %63 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %64 = icmp eq i32 %63, 0
  br i1 %64, label %_L___1, label %bb3.i.i.i

bb3.i.i.i:                                        ; preds = %bb2.i.i.i
  %65 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %66 = icmp eq i32 %65, 1
  br i1 %66, label %_L___1, label %switch_2_default.i.i.i

switch_2_default.i.i.i:                           ; preds = %bb3.i.i.i
  br label %_L___1

__UFO__1:                                         ; preds = %__UFO__1, %bb7
  br label %__UFO__1

_L___1:                                           ; preds = %switch_2_default.i.i.i, %bb3.i.i.i, %bb2.i.i.i, %bb10.i, %switch_7_exp_0.i, %bb1.i, %bb.i, %switch_6_default.i.i, %bb3.i.i, %switch_1_4, %switch_2_default.i.i, %bb3.i.i9, %bb2.i.i8, %switch_2_default.i7.i, %bb3.i6.i, %bb2.i5.i, %switch_2_default.i25.i, %bb3.i24.i, %bb2.i23.i, %bb27.i, %bb3.i49.i, %switch_2_default.i.i.i27, %bb3.i.i.i26, %switch_1_1, %switch_2_default.i.i.i51, %bb3.i.i.i50, %switch_1_0
  %s.0 = phi i32 [ 4, %switch_2_default.i.i.i51 ], [ 4, %switch_2_default.i.i.i27 ], [ 4, %switch_2_default.i25.i ], [ 4, %switch_2_default.i7.i ], [ 4, %switch_2_default.i.i ], [ 4, %switch_6_default.i.i ], [ 4, %switch_2_default.i.i.i ], [ 2, %bb27.i ], [ 4, %switch_1_0 ], [ 4, %bb3.i.i.i50 ], [ 4, %switch_1_1 ], [ 4, %bb3.i.i.i26 ], [ 2, %bb3.i49.i ], [ 4, %bb2.i23.i ], [ 4, %bb3.i24.i ], [ 4, %bb2.i5.i ], [ 4, %bb3.i6.i ], [ 4, %bb2.i.i8 ], [ 4, %bb3.i.i9 ], [ 4, %switch_1_4 ], [ 4, %bb3.i.i ], [ 2, %bb.i ], [ 2, %bb1.i ], [ 2, %switch_7_exp_0.i ], [ 2, %bb10.i ], [ 4, %bb2.i.i.i ], [ 4, %bb3.i.i.i ]
  %lowerDriverReturn.1 = phi i32 [ 259, %switch_2_default.i.i.i51 ], [ 259, %switch_2_default.i.i.i27 ], [ 259, %switch_2_default.i25.i ], [ 259, %switch_2_default.i7.i ], [ 259, %switch_2_default.i.i ], [ 259, %switch_6_default.i.i ], [ 259, %switch_2_default.i.i.i ], [ %returnVal2.0.i51.i.reg2mem.1, %bb27.i ], [ 0, %switch_1_0 ], [ -1073741823, %bb3.i.i.i50 ], [ 0, %switch_1_1 ], [ -1073741823, %bb3.i.i.i26 ], [ 259, %bb3.i49.i ], [ 0, %bb2.i23.i ], [ -1073741823, %bb3.i24.i ], [ 0, %bb2.i5.i ], [ -1073741823, %bb3.i6.i ], [ 0, %bb2.i.i8 ], [ -1073741823, %bb3.i.i9 ], [ 0, %switch_1_4 ], [ -1073741823, %bb3.i.i ], [ 0, %bb.i ], [ 0, %bb1.i ], [ 0, %switch_7_exp_0.i ], [ 0, %bb10.i ], [ 0, %bb2.i.i.i ], [ -1073741823, %bb3.i.i.i ]
  %status.0 = phi i32 [ 259, %switch_2_default.i.i.i51 ], [ 259, %switch_2_default.i.i.i27 ], [ 259, %switch_2_default.i25.i ], [ 0, %switch_2_default.i7.i ], [ 259, %switch_2_default.i.i ], [ 259, %switch_6_default.i.i ], [ 259, %switch_2_default.i.i.i ], [ %returnVal2.0.i51.i.reg2mem.1, %bb27.i ], [ 0, %switch_1_0 ], [ -1073741823, %bb3.i.i.i50 ], [ 0, %switch_1_1 ], [ -1073741823, %bb3.i.i.i26 ], [ 259, %bb3.i49.i ], [ 0, %bb2.i23.i ], [ -1073741823, %bb3.i24.i ], [ 0, %bb2.i5.i ], [ 0, %bb3.i6.i ], [ 0, %bb2.i.i8 ], [ -1073741823, %bb3.i.i9 ], [ 0, %switch_1_4 ], [ -1073741823, %bb3.i.i ], [ -1073741822, %bb.i ], [ -1073741811, %bb1.i ], [ -1073741757, %switch_7_exp_0.i ], [ -1073741811, %bb10.i ], [ 0, %bb2.i.i.i ], [ -1073741823, %bb3.i.i.i ]
  %67 = icmp eq i32 %s.0, 0
  %68 = icmp eq i32 %status.0, -1
  %or.cond = or i1 %68, %67
  %SwitchLeaf29.not = icmp ne i32 %s.0, 4
  %or.cond34.not = or i1 %or.cond, %SwitchLeaf29.not
  %69 = icmp eq i32 %status.0, %lowerDriverReturn.1
  %or.cond35 = or i1 %69, %or.cond34.not
  br i1 %or.cond35, label %__UFO__2, label %bb23

bb23:                                             ; preds = %_L___1
  ret i32 42

__UFO__2:                                         ; preds = %__UFO__2, %_L___1
  br label %__UFO__2
}

declare i32 @ufo.nondet.1()

declare i32 @ufo.nondet.2()
