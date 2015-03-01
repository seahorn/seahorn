; ModuleID = 'floppy_simpl4_false.cil.o3.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-unknown-linux-gnu"

declare i32 @__VERIFIER_nondet_int()

define i32 @main() nounwind {
entry:
  %0 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %1 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %2 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %3 = tail call i32 @ufo.nondet.2() nounwind
  %4 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %5 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %6 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %7 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %8 = tail call i32 @ufo.nondet.2() nounwind
  %9 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %10 = tail call i1 bitcast (i32 ()* @ufo.nondet.1 to i1 ()*)() nounwind
  %11 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %12 = icmp eq i32 %11, 0
  %storemerge = select i1 %12, i32 -1073741637, i32 0
  %13 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %14 = icmp eq i32 %13, 0
  br i1 %14, label %switch_2_break, label %bb4

bb4:                                              ; preds = %entry
  %15 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %16 = icmp eq i32 %15, 1
  br i1 %16, label %switch_2_break, label %bb5

bb5:                                              ; preds = %bb4
  %17 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %18 = icmp eq i32 %17, 2
  %19 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %18, label %switch_2_2, label %bb6

bb6:                                              ; preds = %bb5
  %20 = icmp eq i32 %19, 3
  br i1 %20, label %switch_2_3, label %__UFO__1

switch_2_2:                                       ; preds = %bb5
  %21 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %22 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %23 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %24 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %25 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %26 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %27 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %28 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %29 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %30 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %31 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %32 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %33 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %34 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %35 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %36 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %37 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %38 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %39 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %40 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %41 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %42 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %43 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %44 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %45 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %46 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %47 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %48 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %49 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %50 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %51 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %52 = icmp eq i32 %19, 0
  %53 = icmp eq i32 %32, %40
  %or.cond.i = or i1 %53, %52
  br i1 %or.cond.i, label %bb2.i, label %bb1.i4

bb1.i4:                                           ; preds = %switch_2_2
  %54 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %55 = icmp eq i32 %54, 0
  %s.1 = select i1 %55, i32 1, i32 2
  %pended.0 = zext i1 %55 to i32
  %56 = select i1 %55, i32 259, i32 -1073741536
  br label %switch_2_break

bb2.i:                                            ; preds = %switch_2_2
  %57 = icmp eq i32 %21, 0
  br i1 %57, label %bb4.i, label %switch_2_break

bb4.i:                                            ; preds = %bb2.i
  %58 = icmp eq i32 %22, 0
  br i1 %58, label %bb2.i28.i, label %bb9.i10

bb2.i28.i:                                        ; preds = %bb4.i
  %59 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %60 = icmp eq i32 %59, 0
  br i1 %60, label %switch_2_break, label %bb3.i29.i

bb3.i29.i:                                        ; preds = %bb2.i28.i
  %61 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %62 = icmp eq i32 %61, 1
  br i1 %62, label %switch_2_break, label %switch_8_default.i30.i

switch_8_default.i30.i:                           ; preds = %bb3.i29.i
  br label %switch_2_break

bb9.i10:                                          ; preds = %bb4.i
  %63 = icmp eq i32 %32, %41
  br i1 %63, label %switch_13_exp_0.i, label %bb10.i11

bb10.i11:                                         ; preds = %bb9.i10
  %64 = icmp eq i32 %32, %42
  br i1 %64, label %switch_13_exp_1.i, label %bb11.i12

bb11.i12:                                         ; preds = %bb10.i11
  %65 = icmp eq i32 %32, %43
  %66 = icmp eq i32 %32, %44
  %or.cond1.i = or i1 %66, %65
  br i1 %or.cond1.i, label %switch_13_exp_3.i, label %bb13.i13

bb13.i13:                                         ; preds = %bb11.i12
  %67 = icmp eq i32 %32, %45
  %68 = icmp eq i32 %32, %46
  %69 = icmp eq i32 %32, %47
  %70 = icmp eq i32 %32, %48
  %or.cond2.i = or i1 %68, %67
  %or.cond3.i = or i1 %or.cond2.i, %69
  %or.cond4.i = or i1 %or.cond3.i, %70
  br i1 %or.cond4.i, label %switch_13_exp_7.i, label %bb17.i

bb17.i:                                           ; preds = %bb13.i13
  %71 = icmp eq i32 %32, %49
  %72 = icmp eq i32 %32, %50
  %or.cond5.i = or i1 %72, %71
  br i1 %or.cond5.i, label %switch_13_exp_9.i, label %bb2.i16.i

switch_13_exp_0.i:                                ; preds = %bb9.i10
  %73 = icmp slt i32 %23, %24
  br i1 %73, label %switch_2_break, label %bb23.i

bb23.i:                                           ; preds = %switch_13_exp_0.i
  %74 = add nsw i32 %26, %25
  %75 = icmp slt i32 %23, %74
  br i1 %75, label %switch_13_break.i.thread12, label %switch_2_break

switch_13_exp_1.i:                                ; preds = %bb10.i11
  %76 = icmp eq i32 %27, 0
  %77 = icmp slt i32 %23, %29
  %or.cond7.i = or i1 %77, %76
  br i1 %or.cond7.i, label %switch_2_break, label %bb29.i

bb29.i:                                           ; preds = %switch_13_exp_1.i
  %78 = add nsw i32 %28, %26
  %79 = icmp slt i32 %23, %78
  br i1 %79, label %switch_13_break.i.thread12, label %switch_2_break

switch_13_exp_3.i:                                ; preds = %bb11.i12
  %80 = icmp slt i32 %30, %31
  br i1 %80, label %switch_2_break, label %bb33.i17

bb33.i17:                                         ; preds = %switch_13_exp_3.i
  %81 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %82 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %83 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %84 = icmp eq i32 %81, %82
  %85 = icmp eq i32 %83, 0
  %or.cond.i.i16 = and i1 %85, %84
  br i1 %or.cond.i.i16, label %bb35.i, label %switch_2_break

bb35.i:                                           ; preds = %bb33.i17
  %86 = icmp eq i32 %32, %51
  br i1 %86, label %bb36.i18, label %switch_13_exp_7.i

bb36.i18:                                         ; preds = %bb35.i
  %87 = icmp slt i32 %30, %33
  %88 = icmp slt i32 %30, %39
  %89 = icmp sgt i32 %34, 255
  %90 = icmp sgt i32 %35, 255
  %or.cond8.i = or i1 %89, %87
  %or.cond9.i = or i1 %or.cond8.i, %90
  %or.cond10.i = or i1 %or.cond9.i, %88
  br i1 %or.cond10.i, label %switch_2_break, label %switch_13_exp_7.i

switch_13_exp_7.i:                                ; preds = %bb36.i18, %bb35.i, %bb13.i13
  %91 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %92 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %93 = icmp eq i32 %91, 1
  br i1 %93, label %switch_2_break, label %bb1.i19.i

bb1.i19.i:                                        ; preds = %switch_13_exp_7.i
  %94 = icmp eq i32 %92, -1
  br i1 %94, label %bb2.i20.i, label %return.i

bb2.i20.i:                                        ; preds = %bb1.i19.i
  %95 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %96 = icmp eq i32 %95, 0
  %.0.i.i.i19 = select i1 %96, i32 0, i32 -1073741823
  %97 = icmp slt i32 %.0.i.i.i19, 0
  br i1 %97, label %switch_13_break.i, label %bb4.i.i22

bb4.i.i22:                                        ; preds = %bb2.i20.i
  %98 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %99 = icmp eq i32 %98, 0
  %.0.i2.i.i20 = select i1 %99, i32 0, i32 -1073741823
  %100 = icmp slt i32 %.0.i2.i.i20, 0
  br i1 %100, label %switch_13_break.i, label %return.i

switch_13_exp_9.i:                                ; preds = %bb17.i
  %101 = icmp slt i32 %23, %36
  br i1 %101, label %switch_2_break, label %bb45.i

bb45.i:                                           ; preds = %switch_13_exp_9.i
  %sum = add i32 %37, -1
  %102 = sub i32 %38, %sum
  %103 = icmp slt i32 %23, %102
  %ntStatus.1.i = select i1 %103, i32 -2147483643, i32 0
  br label %switch_13_break.i

bb2.i16.i:                                        ; preds = %bb17.i
  %104 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %105 = icmp eq i32 %104, 0
  br i1 %105, label %switch_2_break, label %bb3.i17.i

bb3.i17.i:                                        ; preds = %bb2.i16.i
  %106 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %107 = icmp eq i32 %106, 1
  br i1 %107, label %switch_2_break, label %switch_8_default.i.i27

switch_8_default.i.i27:                           ; preds = %bb3.i17.i
  br label %switch_2_break

switch_13_break.i.thread12:                       ; preds = %bb29.i, %bb23.i
  br label %switch_2_break

switch_13_break.i:                                ; preds = %bb45.i, %bb4.i.i22, %bb2.i20.i
  %ntStatus.0.i39 = phi i32 [ %ntStatus.1.i, %bb45.i ], [ %.0.i.i.i19, %bb2.i20.i ], [ %.0.i2.i.i20, %bb4.i.i22 ]
  %108 = icmp eq i32 %ntStatus.0.i39, 259
  br i1 %108, label %return.i, label %switch_2_break

return.i:                                         ; preds = %switch_13_break.i, %bb4.i.i22, %bb1.i19.i
  %pended.4.reg2mem.0 = phi i32 [ 1, %bb1.i19.i ], [ 1, %bb4.i.i22 ], [ 0, %switch_13_break.i ]
  %ntStatus.0.i39.reg2mem.0 = phi i32 [ 259, %bb1.i19.i ], [ 259, %bb4.i.i22 ], [ %ntStatus.0.i39, %switch_13_break.i ]
  br label %switch_2_break

switch_2_3:                                       ; preds = %bb6
  %109 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %110 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %111 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %112 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %113 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %114 = icmp eq i32 %109, 0
  br i1 %114, label %NodeBlock102, label %switch_2_break

NodeBlock102:                                     ; preds = %switch_2_3
  %Pivot103 = icmp slt i32 %113, 3
  br i1 %Pivot103, label %NodeBlock86, label %NodeBlock100

NodeBlock100:                                     ; preds = %NodeBlock102
  %Pivot101 = icmp slt i32 %113, 5
  br i1 %Pivot101, label %NodeBlock92, label %NodeBlock98

NodeBlock98:                                      ; preds = %NodeBlock100
  %Pivot99 = icmp slt i32 %113, 6
  br i1 %Pivot99, label %LeafBlock94, label %LeafBlock96

LeafBlock96:                                      ; preds = %NodeBlock98
  %SwitchLeaf97 = icmp eq i32 %113, 6
  br i1 %SwitchLeaf97, label %switch_0_6.i, label %bb2.i.i

LeafBlock94:                                      ; preds = %NodeBlock98
  %SwitchLeaf95 = icmp eq i32 %113, 5
  br i1 %SwitchLeaf95, label %switch_0_5.i, label %bb2.i.i

NodeBlock92:                                      ; preds = %NodeBlock100
  %Pivot93 = icmp slt i32 %113, 4
  br i1 %Pivot93, label %LeafBlock88, label %LeafBlock90

LeafBlock90:                                      ; preds = %NodeBlock92
  %SwitchLeaf91 = icmp eq i32 %113, 4
  br i1 %SwitchLeaf91, label %bb2.i26.i, label %bb2.i.i

LeafBlock88:                                      ; preds = %NodeBlock92
  %SwitchLeaf89 = icmp eq i32 %113, 3
  br i1 %SwitchLeaf89, label %switch_0_6.i, label %bb2.i.i

NodeBlock86:                                      ; preds = %NodeBlock102
  %Pivot87 = icmp slt i32 %113, 1
  br i1 %Pivot87, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock86
  %Pivot = icmp slt i32 %113, 2
  br i1 %Pivot, label %LeafBlock82, label %LeafBlock84

LeafBlock84:                                      ; preds = %NodeBlock
  %SwitchLeaf85 = icmp eq i32 %113, 2
  br i1 %SwitchLeaf85, label %bb2.i7.i, label %bb2.i.i

LeafBlock82:                                      ; preds = %NodeBlock
  %SwitchLeaf83 = icmp eq i32 %113, 1
  br i1 %SwitchLeaf83, label %switch_0_5.i, label %bb2.i.i

LeafBlock:                                        ; preds = %NodeBlock86
  %SwitchLeaf = icmp eq i32 %113, 0
  br i1 %SwitchLeaf, label %switch_0_0.i, label %bb2.i.i

switch_0_0.i:                                     ; preds = %LeafBlock
  %115 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %116 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %117 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %118 = icmp eq i32 %117, 0
  br i1 %118, label %bb6.i152.i, label %bb3.i12.i.i

bb3.i12.i.i:                                      ; preds = %switch_0_0.i
  %119 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %120 = icmp eq i32 %119, 1
  br i1 %120, label %bb6.i152.i, label %bb5.i151.i.bb6.i152.i_crit_edge

bb5.i151.i.bb6.i152.i_crit_edge:                  ; preds = %bb3.i12.i.i
  br label %bb6.i152.i

bb6.i152.i:                                       ; preds = %bb5.i151.i.bb6.i152.i_crit_edge, %bb3.i12.i.i, %switch_0_0.i
  %returnVal2.0.i.i.i.reg2mem.1 = phi i32 [ 259, %bb5.i151.i.bb6.i152.i_crit_edge ], [ 0, %switch_0_0.i ], [ -1073741823, %bb3.i12.i.i ]
  %121 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %122 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %123 = icmp eq i32 %121, 0
  %not.9 = icmp ne i32 %122, 0
  %124 = or i1 %not.9, %123
  br i1 %124, label %switch_2_break, label %bb.i2.i.i.i

bb.i2.i.i.i:                                      ; preds = %bb6.i152.i
  %125 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %126 = icmp eq i32 %125, 0
  br i1 %126, label %FlFdcDeviceIo.exit.i.i, label %bb3.i5.i.i.i

bb3.i5.i.i.i:                                     ; preds = %bb.i2.i.i.i
  %127 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %128 = icmp eq i32 %127, 1
  br i1 %128, label %FlFdcDeviceIo.exit.i.i, label %bb2.i.i.i

bb2.i.i.i:                                        ; preds = %bb3.i5.i.i.i
  br label %FlFdcDeviceIo.exit.i.i

FlFdcDeviceIo.exit.i.i:                           ; preds = %bb2.i.i.i, %bb3.i5.i.i.i, %bb.i2.i.i.i
  %lowerDriverReturn.9 = phi i32 [ 259, %bb2.i.i.i ], [ 0, %bb.i2.i.i.i ], [ -1073741823, %bb3.i5.i.i.i ]
  %129 = phi i32 [ %storemerge, %bb2.i.i.i ], [ 0, %bb.i2.i.i.i ], [ -1073741823, %bb3.i5.i.i.i ]
  %130 = icmp slt i32 %129, 0
  br i1 %130, label %switch_2_break, label %bb7.i153.i

bb7.i153.i:                                       ; preds = %FlFdcDeviceIo.exit.i.i
  %131 = icmp eq i32 %115, 0
  %132 = icmp eq i32 %116, 0
  %or.cond.i.i = or i1 %132, %131
  br i1 %or.cond.i.i, label %while_1_break.i.i, label %bb13.i158.i

while_1_break.i.i:                                ; preds = %bb7.i153.i
  %133 = icmp slt i32 %129, 0
  br i1 %133, label %switch_2_break, label %bb13.i158.i

bb13.i158.i:                                      ; preds = %while_1_break.i.i, %bb7.i153.i
  %ntStatus.0.i.i.reg2mem.0 = phi i32 [ 0, %bb7.i153.i ], [ %129, %while_1_break.i.i ]
  %134 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %switch_2_break

switch_0_5.i:                                     ; preds = %LeafBlock82, %LeafBlock94
  %135 = icmp eq i32 %110, 0
  %136 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %135, label %bb2.i131.i, label %bb13.i

bb2.i131.i:                                       ; preds = %switch_0_5.i
  %137 = icmp eq i32 %136, 0
  br i1 %137, label %switch_2_break, label %bb3.i132.i

bb3.i132.i:                                       ; preds = %bb2.i131.i
  %138 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %139 = icmp eq i32 %138, 1
  br i1 %139, label %switch_2_break, label %switch_8_default.i133.i

switch_8_default.i133.i:                          ; preds = %bb3.i132.i
  br label %switch_2_break

bb13.i:                                           ; preds = %switch_0_5.i
  %140 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %141 = icmp eq i32 %136, 1
  br i1 %141, label %switch_2_break, label %bb1.i121.i

bb1.i121.i:                                       ; preds = %bb13.i
  %142 = icmp eq i32 %140, -1
  br i1 %142, label %bb2.i122.i, label %bb2.i96.i

bb2.i122.i:                                       ; preds = %bb1.i121.i
  %143 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %144 = icmp eq i32 %143, 0
  %.0.i.i.i = select i1 %144, i32 0, i32 -1073741823
  %145 = icmp slt i32 %.0.i.i.i, 0
  br i1 %145, label %FlQueueIrpToThread.exit.i, label %bb4.i124.i

bb4.i124.i:                                       ; preds = %bb2.i122.i
  %146 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %147 = icmp eq i32 %146, 0
  %.0.i2.i.i = select i1 %147, i32 0, i32 -1073741823
  %148 = icmp slt i32 %.0.i2.i.i, 0
  br i1 %148, label %FlQueueIrpToThread.exit.i, label %bb2.i96.i

FlQueueIrpToThread.exit.i:                        ; preds = %bb4.i124.i, %bb2.i122.i
  %149 = phi i32 [ %.0.i.i.i, %bb2.i122.i ], [ %.0.i2.i.i, %bb4.i124.i ]
  %150 = icmp eq i32 %149, 259
  br i1 %150, label %bb2.i96.i, label %switch_2_break

bb2.i96.i:                                        ; preds = %FlQueueIrpToThread.exit.i, %bb4.i124.i, %bb1.i121.i
  %pended.5.reg2mem.0 = phi i32 [ 1, %bb1.i121.i ], [ 1, %bb4.i124.i ], [ 0, %FlQueueIrpToThread.exit.i ]
  %151 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %152 = icmp eq i32 %151, 0
  br i1 %152, label %switch_2_break, label %bb3.i97.i

bb3.i97.i:                                        ; preds = %bb2.i96.i
  %153 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %154 = icmp eq i32 %153, 1
  br i1 %154, label %switch_2_break, label %switch_8_default.i98.i

switch_8_default.i98.i:                           ; preds = %bb3.i97.i
  br label %switch_2_break

switch_0_6.i:                                     ; preds = %LeafBlock88, %LeafBlock96
  %155 = icmp eq i32 %110, 0
  %156 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %157 = icmp eq i32 %156, 0
  br i1 %155, label %bb2.i74.i, label %bb2.i54.i

bb2.i74.i:                                        ; preds = %switch_0_6.i
  br i1 %157, label %switch_2_break, label %bb3.i75.i

bb3.i75.i:                                        ; preds = %bb2.i74.i
  %158 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %159 = icmp eq i32 %158, 1
  br i1 %159, label %switch_2_break, label %switch_8_default.i76.i

switch_8_default.i76.i:                           ; preds = %bb3.i75.i
  br label %switch_2_break

bb2.i54.i:                                        ; preds = %switch_0_6.i
  br i1 %157, label %bb7.i63.i, label %bb3.i55.i

bb3.i55.i:                                        ; preds = %bb2.i54.i
  %160 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %161 = icmp eq i32 %160, 1
  br i1 %161, label %bb7.i63.i, label %bb30.i

bb7.i63.i:                                        ; preds = %bb3.i55.i, %bb2.i54.i
  %returnVal2.0.i57.i = phi i32 [ 0, %bb2.i54.i ], [ -1073741823, %bb3.i55.i ]
  %162 = icmp eq i32 %returnVal2.0.i57.i, 259
  %storemerge.i62.i = select i1 %162, i32 6, i32 1
  br i1 %162, label %bb30.i, label %bb31.i

bb30.i:                                           ; preds = %bb7.i63.i, %bb3.i55.i
  %returnVal2.0.i57.i.reg2mem.0 = phi i32 [ 259, %bb3.i55.i ], [ %returnVal2.0.i57.i, %bb7.i63.i ]
  %storemerge.i62.i.reg2mem.0 = phi i32 [ 6, %bb3.i55.i ], [ %storemerge.i62.i, %bb7.i63.i ]
  %storemerge.i62.i.reload67 = phi i32 [ 6, %bb3.i55.i ], [ %storemerge.i62.i, %bb7.i63.i ]
  %163 = icmp eq i32 %storemerge.i62.i.reload67, 6
  br i1 %163, label %switch_2_break, label %bb31.i

bb31.i:                                           ; preds = %bb30.i, %bb7.i63.i
  %returnVal2.0.i57.i.reg2mem.1 = phi i32 [ %returnVal2.0.i57.i, %bb7.i63.i ], [ %returnVal2.0.i57.i.reg2mem.0, %bb30.i ]
  %s.28 = phi i32 [ %storemerge.i62.i, %bb7.i63.i ], [ %storemerge.i62.i.reg2mem.0, %bb30.i ]
  %ntStatus.3.i = phi i32 [ %returnVal2.0.i57.i, %bb7.i63.i ], [ 0, %bb30.i ]
  %164 = icmp eq i32 %s.28, 1
  br i1 %164, label %switch_2_break, label %UnifiedReturnBlock

bb2.i26.i:                                        ; preds = %LeafBlock90
  %165 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %166 = icmp eq i32 %165, 0
  br i1 %166, label %switch_2_break, label %bb3.i27.i

bb3.i27.i:                                        ; preds = %bb2.i26.i
  %167 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %168 = icmp eq i32 %167, 1
  br i1 %168, label %switch_2_break, label %switch_8_default.i28.i

switch_8_default.i28.i:                           ; preds = %bb3.i27.i
  br label %switch_2_break

bb2.i7.i:                                         ; preds = %LeafBlock84
  %169 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %170 = icmp eq i32 %169, 0
  br i1 %170, label %switch_2_break, label %bb3.i8.i

bb3.i8.i:                                         ; preds = %bb2.i7.i
  %171 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %172 = icmp eq i32 %171, 1
  br i1 %172, label %switch_2_break, label %switch_8_default.i9.i

switch_8_default.i9.i:                            ; preds = %bb3.i8.i
  br label %switch_2_break

bb2.i.i:                                          ; preds = %LeafBlock, %LeafBlock82, %LeafBlock84, %LeafBlock88, %LeafBlock90, %LeafBlock94, %LeafBlock96
  %173 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %174 = icmp eq i32 %173, 0
  br i1 %174, label %switch_2_break, label %bb3.i.i

bb3.i.i:                                          ; preds = %bb2.i.i
  %175 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %176 = icmp eq i32 %175, 1
  br i1 %176, label %switch_2_break, label %switch_8_default.i.i

switch_8_default.i.i:                             ; preds = %bb3.i.i
  br label %switch_2_break

__UFO__1:                                         ; preds = %__UFO__1, %bb6
  br label %__UFO__1

switch_2_break:                                   ; preds = %switch_8_default.i.i, %bb3.i.i, %bb2.i.i, %switch_8_default.i9.i, %bb3.i8.i, %bb2.i7.i, %switch_8_default.i28.i, %bb3.i27.i, %bb2.i26.i, %bb31.i, %bb30.i, %switch_8_default.i76.i, %bb3.i75.i, %bb2.i74.i, %switch_8_default.i98.i, %bb3.i97.i, %bb2.i96.i, %FlQueueIrpToThread.exit.i, %bb13.i, %switch_8_default.i133.i, %bb3.i132.i, %bb2.i131.i, %bb13.i158.i, %while_1_break.i.i, %FlFdcDeviceIo.exit.i.i, %bb6.i152.i, %switch_2_3, %return.i, %switch_13_break.i, %switch_13_break.i.thread12, %switch_8_default.i.i27, %bb3.i17.i, %bb2.i16.i, %switch_13_exp_9.i, %switch_13_exp_7.i, %bb36.i18, %bb33.i17, %switch_13_exp_3.i, %bb29.i, %switch_13_exp_1.i, %bb23.i, %switch_13_exp_0.i, %switch_8_default.i30.i, %bb3.i29.i, %bb2.i28.i, %bb2.i, %bb1.i4, %bb4, %entry
  %s.0 = phi i32 [ 1, %return.i ], [ %s.1, %bb1.i4 ], [ 4, %switch_8_default.i30.i ], [ 4, %switch_8_default.i.i27 ], [ 4, %switch_8_default.i133.i ], [ 4, %switch_8_default.i98.i ], [ 4, %switch_8_default.i76.i ], [ 4, %switch_8_default.i28.i ], [ 4, %switch_8_default.i.i ], [ 4, %switch_8_default.i9.i ], [ 2, %switch_13_break.i.thread12 ], [ 2, %entry ], [ 2, %bb4 ], [ 2, %bb2.i ], [ 4, %bb2.i28.i ], [ 4, %bb3.i29.i ], [ 2, %switch_13_exp_0.i ], [ 2, %bb23.i ], [ 2, %switch_13_exp_1.i ], [ 2, %bb29.i ], [ 2, %switch_13_exp_3.i ], [ 2, %bb33.i17 ], [ 2, %bb36.i18 ], [ 2, %switch_13_exp_7.i ], [ 2, %switch_13_exp_9.i ], [ 4, %bb2.i16.i ], [ 4, %bb3.i17.i ], [ 2, %switch_13_break.i ], [ 2, %switch_2_3 ], [ 2, %while_1_break.i.i ], [ 2, %FlFdcDeviceIo.exit.i.i ], [ 2, %bb6.i152.i ], [ 2, %bb13.i158.i ], [ 4, %bb2.i131.i ], [ 4, %bb3.i132.i ], [ 2, %bb13.i ], [ 2, %FlQueueIrpToThread.exit.i ], [ 4, %bb2.i96.i ], [ 4, %bb3.i97.i ], [ 4, %bb2.i74.i ], [ 4, %bb3.i75.i ], [ 2, %bb30.i ], [ 2, %bb31.i ], [ 4, %bb2.i26.i ], [ 4, %bb3.i27.i ], [ 4, %bb2.i7.i ], [ 4, %bb3.i8.i ], [ 4, %bb2.i.i ], [ 4, %bb3.i.i ]
  %pended.2 = phi i32 [ %pended.4.reg2mem.0, %return.i ], [ %pended.0, %bb1.i4 ], [ 0, %switch_8_default.i30.i ], [ 0, %switch_8_default.i.i27 ], [ 0, %switch_8_default.i133.i ], [ %pended.5.reg2mem.0, %switch_8_default.i98.i ], [ 0, %switch_8_default.i76.i ], [ 0, %switch_8_default.i28.i ], [ 0, %switch_8_default.i.i ], [ 0, %switch_8_default.i9.i ], [ 0, %switch_13_break.i.thread12 ], [ 0, %entry ], [ 0, %bb4 ], [ 0, %bb2.i ], [ 0, %bb2.i28.i ], [ 0, %bb3.i29.i ], [ 0, %switch_13_exp_0.i ], [ 0, %bb23.i ], [ 0, %switch_13_exp_1.i ], [ 0, %bb29.i ], [ 0, %switch_13_exp_3.i ], [ 0, %bb33.i17 ], [ 0, %bb36.i18 ], [ 0, %switch_13_exp_7.i ], [ 0, %switch_13_exp_9.i ], [ 0, %bb2.i16.i ], [ 0, %bb3.i17.i ], [ 0, %switch_13_break.i ], [ 0, %switch_2_3 ], [ 0, %while_1_break.i.i ], [ 0, %FlFdcDeviceIo.exit.i.i ], [ 0, %bb6.i152.i ], [ 0, %bb13.i158.i ], [ 0, %bb2.i131.i ], [ 0, %bb3.i132.i ], [ 0, %bb13.i ], [ 0, %FlQueueIrpToThread.exit.i ], [ %pended.5.reg2mem.0, %bb2.i96.i ], [ %pended.5.reg2mem.0, %bb3.i97.i ], [ 0, %bb2.i74.i ], [ 0, %bb3.i75.i ], [ 0, %bb30.i ], [ 0, %bb31.i ], [ 0, %bb2.i26.i ], [ 0, %bb3.i27.i ], [ 0, %bb2.i7.i ], [ 0, %bb3.i8.i ], [ 0, %bb2.i.i ], [ 0, %bb3.i.i ]
  %lowerDriverReturn.2 = phi i32 [ 0, %return.i ], [ 0, %bb1.i4 ], [ 259, %switch_8_default.i30.i ], [ 259, %switch_8_default.i.i27 ], [ 259, %switch_8_default.i133.i ], [ 259, %switch_8_default.i98.i ], [ 259, %switch_8_default.i76.i ], [ 259, %switch_8_default.i28.i ], [ 259, %switch_8_default.i.i ], [ 259, %switch_8_default.i9.i ], [ 0, %switch_13_break.i.thread12 ], [ 0, %entry ], [ 0, %bb4 ], [ 0, %bb2.i ], [ 0, %bb2.i28.i ], [ -1073741823, %bb3.i29.i ], [ 0, %switch_13_exp_0.i ], [ 0, %bb23.i ], [ 0, %switch_13_exp_1.i ], [ 0, %bb29.i ], [ 0, %switch_13_exp_3.i ], [ 0, %bb33.i17 ], [ 0, %bb36.i18 ], [ 0, %switch_13_exp_7.i ], [ 0, %switch_13_exp_9.i ], [ 0, %bb2.i16.i ], [ -1073741823, %bb3.i17.i ], [ 0, %switch_13_break.i ], [ 0, %switch_2_3 ], [ %lowerDriverReturn.9, %bb13.i158.i ], [ %returnVal2.0.i.i.i.reg2mem.1, %bb6.i152.i ], [ %lowerDriverReturn.9, %FlFdcDeviceIo.exit.i.i ], [ %lowerDriverReturn.9, %while_1_break.i.i ], [ 0, %bb2.i131.i ], [ -1073741823, %bb3.i132.i ], [ 0, %bb13.i ], [ 0, %FlQueueIrpToThread.exit.i ], [ 0, %bb2.i96.i ], [ -1073741823, %bb3.i97.i ], [ 0, %bb2.i74.i ], [ -1073741823, %bb3.i75.i ], [ %returnVal2.0.i57.i.reg2mem.0, %bb30.i ], [ %returnVal2.0.i57.i.reg2mem.1, %bb31.i ], [ 0, %bb2.i26.i ], [ -1073741823, %bb3.i27.i ], [ 0, %bb2.i7.i ], [ -1073741823, %bb3.i8.i ], [ 0, %bb2.i.i ], [ -1073741823, %bb3.i.i ]
  %status.0 = phi i32 [ %56, %bb1.i4 ], [ %ntStatus.0.i39.reg2mem.0, %return.i ], [ 259, %switch_8_default.i30.i ], [ 259, %switch_8_default.i.i27 ], [ 259, %switch_8_default.i133.i ], [ 259, %switch_8_default.i98.i ], [ 259, %switch_8_default.i76.i ], [ 259, %switch_8_default.i28.i ], [ 259, %switch_8_default.i.i ], [ 259, %switch_8_default.i9.i ], [ -2147483643, %switch_13_break.i.thread12 ], [ 0, %entry ], [ 0, %bb4 ], [ -1073741738, %bb2.i ], [ 0, %bb2.i28.i ], [ -1073741823, %bb3.i29.i ], [ -1073741811, %switch_13_exp_0.i ], [ 0, %bb23.i ], [ -1073741811, %switch_13_exp_1.i ], [ 0, %bb29.i ], [ -1073741811, %switch_13_exp_3.i ], [ -1073741811, %bb33.i17 ], [ -1073741811, %bb36.i18 ], [ -1073741101, %switch_13_exp_7.i ], [ -1073741789, %switch_13_exp_9.i ], [ 0, %bb2.i16.i ], [ -1073741823, %bb3.i17.i ], [ %ntStatus.0.i39, %switch_13_break.i ], [ -1073741738, %switch_2_3 ], [ %ntStatus.0.i.i.reg2mem.0, %bb13.i158.i ], [ -1073741670, %bb6.i152.i ], [ %129, %FlFdcDeviceIo.exit.i.i ], [ %129, %while_1_break.i.i ], [ 0, %bb2.i131.i ], [ -1073741823, %bb3.i132.i ], [ -1073741823, %bb13.i ], [ -1073741823, %FlQueueIrpToThread.exit.i ], [ 0, %bb2.i96.i ], [ -1073741823, %bb3.i97.i ], [ 0, %bb2.i74.i ], [ -1073741823, %bb3.i75.i ], [ 0, %bb30.i ], [ %ntStatus.3.i, %bb31.i ], [ 0, %bb2.i26.i ], [ -1073741823, %bb3.i27.i ], [ 0, %bb2.i7.i ], [ -1073741823, %bb3.i8.i ], [ 0, %bb2.i.i ], [ -1073741823, %bb3.i.i ]
  %177 = icmp eq i32 %pended.2, 1
  %178 = icmp eq i32 %s.0, 1
  %or.cond25 = and i1 %177, %178
  br i1 %or.cond25, label %__UFO__2, label %_L___2

_L___2:                                           ; preds = %switch_2_break
  %179 = icmp eq i32 %s.0, 6
  %or.cond26 = and i1 %177, %179
  br i1 %or.cond26, label %__UFO__2, label %_L___1

_L___1:                                           ; preds = %_L___2
  %180 = icmp eq i32 %s.0, 0
  %181 = icmp eq i32 %status.0, -1
  %or.cond = or i1 %181, %180
  br i1 %or.cond, label %__UFO__2, label %NodeBlock113

NodeBlock113:                                     ; preds = %_L___1
  %Pivot114 = icmp ult i32 %s.0, 4
  br i1 %Pivot114, label %LeafBlock105, label %NodeBlock119

NodeBlock119:                                     ; preds = %NodeBlock113
  switch i32 %s.0, label %UnifiedReturnBlock [
    i32 7, label %_L___0
    i32 4, label %_L___0
  ]

LeafBlock105:                                     ; preds = %NodeBlock113
  %SwitchLeaf106 = icmp eq i32 %s.0, 2
  br i1 %SwitchLeaf106, label %_L___0, label %UnifiedReturnBlock

_L___0:                                           ; preds = %LeafBlock105, %NodeBlock119, %NodeBlock119
  br i1 %177, label %bb17, label %bb20

bb17:                                             ; preds = %_L___0
  %182 = icmp eq i32 %status.0, 259
  br i1 %182, label %__UFO__2, label %UnifiedReturnBlock

bb20:                                             ; preds = %_L___0
  %183 = icmp eq i32 %s.0, 2
  br i1 %183, label %bb21, label %bb24

bb21:                                             ; preds = %bb20
  %184 = icmp eq i32 %status.0, 259
  br i1 %184, label %UnifiedReturnBlock, label %__UFO__2

bb24:                                             ; preds = %bb20
  %185 = icmp eq i32 %status.0, %lowerDriverReturn.2
  br i1 %185, label %__UFO__2, label %UnifiedReturnBlock

__UFO__2:                                         ; preds = %__UFO__2, %bb24, %bb21, %bb17, %_L___1, %_L___2, %switch_2_break
  br label %__UFO__2

UnifiedReturnBlock:                               ; preds = %bb24, %bb21, %bb17, %LeafBlock105, %NodeBlock119, %bb31.i
  ret i32 42
}

declare i32 @ufo.nondet.1()

declare i32 @ufo.nondet.2()
