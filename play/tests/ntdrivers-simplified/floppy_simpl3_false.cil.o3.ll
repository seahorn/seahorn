; ModuleID = 'floppy_simpl3_false.cil.o3.bc'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-unknown-linux-gnu"

declare i32 @__VERIFIER_nondet_int()

define i32 @main() nounwind {
entry:
  %0 = tail call i1 @ufo.nondet.2() nounwind
  %1 = tail call i1 @ufo.nondet.2() nounwind
  %2 = tail call i1 @ufo.nondet.2() nounwind
  %3 = tail call i32 @ufo.nondet.1() nounwind
  %4 = tail call i1 @ufo.nondet.2() nounwind
  %5 = tail call i1 @ufo.nondet.2() nounwind
  %6 = tail call i1 @ufo.nondet.2() nounwind
  %7 = tail call i1 @ufo.nondet.2() nounwind
  %8 = tail call i32 @ufo.nondet.1() nounwind
  %9 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %10 = icmp eq i32 %9, 0
  %storemerge = select i1 %10, i32 -1073741637, i32 0
  %11 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %12 = icmp eq i32 %11, 3
  br i1 %12, label %switch_2_3, label %__UFO__1

switch_2_3:                                       ; preds = %entry
  %13 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %14 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %15 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %16 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %17 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %18 = icmp eq i32 %13, 0
  br i1 %18, label %NodeBlock78, label %FloppyPnp.exit

NodeBlock78:                                      ; preds = %switch_2_3
  %Pivot79 = icmp slt i32 %17, 3
  br i1 %Pivot79, label %NodeBlock62, label %NodeBlock76

NodeBlock76:                                      ; preds = %NodeBlock78
  %Pivot77 = icmp slt i32 %17, 5
  br i1 %Pivot77, label %NodeBlock68, label %NodeBlock74

NodeBlock74:                                      ; preds = %NodeBlock76
  %Pivot75 = icmp slt i32 %17, 6
  br i1 %Pivot75, label %LeafBlock70, label %LeafBlock72

LeafBlock72:                                      ; preds = %NodeBlock74
  %SwitchLeaf73 = icmp eq i32 %17, 6
  br i1 %SwitchLeaf73, label %switch_0_6.i, label %bb2.i.i

LeafBlock70:                                      ; preds = %NodeBlock74
  %SwitchLeaf71 = icmp eq i32 %17, 5
  br i1 %SwitchLeaf71, label %switch_0_5.i, label %bb2.i.i

NodeBlock68:                                      ; preds = %NodeBlock76
  %Pivot69 = icmp slt i32 %17, 4
  br i1 %Pivot69, label %LeafBlock64, label %LeafBlock66

LeafBlock66:                                      ; preds = %NodeBlock68
  %SwitchLeaf67 = icmp eq i32 %17, 4
  br i1 %SwitchLeaf67, label %bb2.i26.i, label %bb2.i.i

LeafBlock64:                                      ; preds = %NodeBlock68
  %SwitchLeaf65 = icmp eq i32 %17, 3
  br i1 %SwitchLeaf65, label %switch_0_6.i, label %bb2.i.i

NodeBlock62:                                      ; preds = %NodeBlock78
  %Pivot63 = icmp slt i32 %17, 1
  br i1 %Pivot63, label %LeafBlock, label %NodeBlock

NodeBlock:                                        ; preds = %NodeBlock62
  %Pivot = icmp slt i32 %17, 2
  br i1 %Pivot, label %LeafBlock58, label %LeafBlock60

LeafBlock60:                                      ; preds = %NodeBlock
  %SwitchLeaf61 = icmp eq i32 %17, 2
  br i1 %SwitchLeaf61, label %bb2.i7.i, label %bb2.i.i

LeafBlock58:                                      ; preds = %NodeBlock
  %SwitchLeaf59 = icmp eq i32 %17, 1
  br i1 %SwitchLeaf59, label %switch_0_5.i, label %bb2.i.i

LeafBlock:                                        ; preds = %NodeBlock62
  %SwitchLeaf = icmp eq i32 %17, 0
  br i1 %SwitchLeaf, label %switch_0_0.i, label %bb2.i.i

switch_0_0.i:                                     ; preds = %LeafBlock
  %19 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %20 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %21 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %22 = icmp eq i32 %21, 0
  br i1 %22, label %bb6.i152.i, label %bb3.i12.i.i

bb3.i12.i.i:                                      ; preds = %switch_0_0.i
  %23 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %24 = icmp eq i32 %23, 1
  br i1 %24, label %bb6.i152.i, label %bb5.i151.i.bb6.i152.i_crit_edge

bb5.i151.i.bb6.i152.i_crit_edge:                  ; preds = %bb3.i12.i.i
  br label %bb6.i152.i

bb6.i152.i:                                       ; preds = %bb5.i151.i.bb6.i152.i_crit_edge, %bb3.i12.i.i, %switch_0_0.i
  %returnVal2.0.i.i.i.reg2mem.1 = phi i32 [ 259, %bb5.i151.i.bb6.i152.i_crit_edge ], [ 0, %switch_0_0.i ], [ -1073741823, %bb3.i12.i.i ]
  %25 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %26 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %27 = icmp eq i32 %25, 0
  %not.5 = icmp ne i32 %26, 0
  %28 = or i1 %not.5, %27
  br i1 %28, label %FloppyPnp.exit, label %bb.i2.i.i.i

bb.i2.i.i.i:                                      ; preds = %bb6.i152.i
  %29 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %30 = icmp eq i32 %29, 0
  br i1 %30, label %FlFdcDeviceIo.exit.i.i, label %bb3.i5.i.i.i

bb3.i5.i.i.i:                                     ; preds = %bb.i2.i.i.i
  %31 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %32 = icmp eq i32 %31, 1
  br i1 %32, label %FlFdcDeviceIo.exit.i.i, label %bb2.i.i.i

bb2.i.i.i:                                        ; preds = %bb3.i5.i.i.i
  br label %FlFdcDeviceIo.exit.i.i

FlFdcDeviceIo.exit.i.i:                           ; preds = %bb2.i.i.i, %bb3.i5.i.i.i, %bb.i2.i.i.i
  %lowerDriverReturn.5 = phi i32 [ 259, %bb2.i.i.i ], [ 0, %bb.i2.i.i.i ], [ -1073741823, %bb3.i5.i.i.i ]
  %33 = phi i32 [ %storemerge, %bb2.i.i.i ], [ 0, %bb.i2.i.i.i ], [ -1073741823, %bb3.i5.i.i.i ]
  %34 = icmp slt i32 %33, 0
  br i1 %34, label %FloppyPnp.exit, label %bb7.i153.i

bb7.i153.i:                                       ; preds = %FlFdcDeviceIo.exit.i.i
  %35 = icmp eq i32 %19, 0
  %36 = icmp eq i32 %20, 0
  %or.cond.i.i = or i1 %36, %35
  br i1 %or.cond.i.i, label %while_1_break.i.i, label %bb13.i158.i

while_1_break.i.i:                                ; preds = %bb7.i153.i
  %37 = icmp slt i32 %33, 0
  br i1 %37, label %FloppyPnp.exit, label %bb13.i158.i

bb13.i158.i:                                      ; preds = %while_1_break.i.i, %bb7.i153.i
  %ntStatus.0.i.i.reg2mem.0 = phi i32 [ 0, %bb7.i153.i ], [ %33, %while_1_break.i.i ]
  %38 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br label %FloppyPnp.exit

switch_0_5.i:                                     ; preds = %LeafBlock58, %LeafBlock70
  %39 = icmp eq i32 %14, 0
  %40 = tail call i32 @__VERIFIER_nondet_int() nounwind
  br i1 %39, label %bb2.i131.i, label %bb13.i

bb2.i131.i:                                       ; preds = %switch_0_5.i
  %41 = icmp eq i32 %40, 0
  br i1 %41, label %FloppyPnp.exit, label %bb3.i132.i

bb3.i132.i:                                       ; preds = %bb2.i131.i
  %42 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %43 = icmp eq i32 %42, 1
  br i1 %43, label %FloppyPnp.exit, label %switch_8_default.i133.i

switch_8_default.i133.i:                          ; preds = %bb3.i132.i
  br label %FloppyPnp.exit

bb13.i:                                           ; preds = %switch_0_5.i
  %44 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %45 = icmp eq i32 %40, 1
  br i1 %45, label %FloppyPnp.exit, label %bb1.i121.i

bb1.i121.i:                                       ; preds = %bb13.i
  %46 = icmp eq i32 %44, -1
  br i1 %46, label %bb2.i122.i, label %bb2.i96.i

bb2.i122.i:                                       ; preds = %bb1.i121.i
  %47 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %48 = icmp eq i32 %47, 0
  %.0.i.i.i = select i1 %48, i32 0, i32 -1073741823
  %49 = icmp slt i32 %.0.i.i.i, 0
  br i1 %49, label %FlQueueIrpToThread.exit.i, label %bb4.i124.i

bb4.i124.i:                                       ; preds = %bb2.i122.i
  %50 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %51 = icmp eq i32 %50, 0
  %.0.i2.i.i = select i1 %51, i32 0, i32 -1073741823
  %52 = icmp slt i32 %.0.i2.i.i, 0
  br i1 %52, label %FlQueueIrpToThread.exit.i, label %bb2.i96.i

FlQueueIrpToThread.exit.i:                        ; preds = %bb4.i124.i, %bb2.i122.i
  %53 = phi i32 [ %.0.i.i.i, %bb2.i122.i ], [ %.0.i2.i.i, %bb4.i124.i ]
  %54 = icmp eq i32 %53, 259
  br i1 %54, label %bb2.i96.i, label %FloppyPnp.exit

bb2.i96.i:                                        ; preds = %FlQueueIrpToThread.exit.i, %bb4.i124.i, %bb1.i121.i
  %pended.0.reg2mem.0 = phi i32 [ 1, %bb1.i121.i ], [ 1, %bb4.i124.i ], [ 0, %FlQueueIrpToThread.exit.i ]
  %55 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %56 = icmp eq i32 %55, 0
  br i1 %56, label %FloppyPnp.exit, label %bb3.i97.i

bb3.i97.i:                                        ; preds = %bb2.i96.i
  %57 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %58 = icmp eq i32 %57, 1
  br i1 %58, label %FloppyPnp.exit, label %switch_8_default.i98.i

switch_8_default.i98.i:                           ; preds = %bb3.i97.i
  br label %FloppyPnp.exit

switch_0_6.i:                                     ; preds = %LeafBlock64, %LeafBlock72
  %59 = icmp eq i32 %14, 0
  %60 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %61 = icmp eq i32 %60, 0
  br i1 %59, label %bb2.i74.i, label %bb2.i54.i

bb2.i74.i:                                        ; preds = %switch_0_6.i
  br i1 %61, label %FloppyPnp.exit, label %bb3.i75.i

bb3.i75.i:                                        ; preds = %bb2.i74.i
  %62 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %63 = icmp eq i32 %62, 1
  br i1 %63, label %FloppyPnp.exit, label %switch_8_default.i76.i

switch_8_default.i76.i:                           ; preds = %bb3.i75.i
  br label %FloppyPnp.exit

bb2.i54.i:                                        ; preds = %switch_0_6.i
  br i1 %61, label %bb7.i63.i, label %bb3.i55.i

bb3.i55.i:                                        ; preds = %bb2.i54.i
  %64 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %65 = icmp eq i32 %64, 1
  br i1 %65, label %bb7.i63.i, label %bb30.i

bb7.i63.i:                                        ; preds = %bb3.i55.i, %bb2.i54.i
  %returnVal2.0.i57.i = phi i32 [ 0, %bb2.i54.i ], [ -1073741823, %bb3.i55.i ]
  %66 = icmp eq i32 %returnVal2.0.i57.i, 259
  %storemerge.i62.i = select i1 %66, i32 6, i32 1
  br i1 %66, label %bb30.i, label %bb31.i

bb30.i:                                           ; preds = %bb7.i63.i, %bb3.i55.i
  %returnVal2.0.i57.i.reg2mem.0 = phi i32 [ 259, %bb3.i55.i ], [ %returnVal2.0.i57.i, %bb7.i63.i ]
  %storemerge.i62.i.reg2mem.0 = phi i32 [ 6, %bb3.i55.i ], [ %storemerge.i62.i, %bb7.i63.i ]
  %storemerge.i62.i.reload43 = phi i32 [ 6, %bb3.i55.i ], [ %storemerge.i62.i, %bb7.i63.i ]
  %67 = icmp eq i32 %storemerge.i62.i.reload43, 6
  br i1 %67, label %FloppyPnp.exit, label %bb31.i

bb31.i:                                           ; preds = %bb30.i, %bb7.i63.i
  %returnVal2.0.i57.i.reg2mem.1 = phi i32 [ %returnVal2.0.i57.i, %bb7.i63.i ], [ %returnVal2.0.i57.i.reg2mem.0, %bb30.i ]
  %s.21 = phi i32 [ %storemerge.i62.i, %bb7.i63.i ], [ %storemerge.i62.i.reg2mem.0, %bb30.i ]
  %ntStatus.3.i = phi i32 [ %returnVal2.0.i57.i, %bb7.i63.i ], [ 0, %bb30.i ]
  %68 = icmp eq i32 %s.21, 1
  br i1 %68, label %FloppyPnp.exit, label %UnifiedReturnBlock

bb2.i26.i:                                        ; preds = %LeafBlock66
  %69 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %70 = icmp eq i32 %69, 0
  br i1 %70, label %FloppyPnp.exit, label %bb3.i27.i

bb3.i27.i:                                        ; preds = %bb2.i26.i
  %71 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %72 = icmp eq i32 %71, 1
  br i1 %72, label %FloppyPnp.exit, label %switch_8_default.i28.i

switch_8_default.i28.i:                           ; preds = %bb3.i27.i
  br label %FloppyPnp.exit

bb2.i7.i:                                         ; preds = %LeafBlock60
  %73 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %74 = icmp eq i32 %73, 0
  br i1 %74, label %FloppyPnp.exit, label %bb3.i8.i

bb3.i8.i:                                         ; preds = %bb2.i7.i
  %75 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %76 = icmp eq i32 %75, 1
  br i1 %76, label %FloppyPnp.exit, label %switch_8_default.i9.i

switch_8_default.i9.i:                            ; preds = %bb3.i8.i
  br label %FloppyPnp.exit

bb2.i.i:                                          ; preds = %LeafBlock, %LeafBlock58, %LeafBlock60, %LeafBlock64, %LeafBlock66, %LeafBlock70, %LeafBlock72
  %77 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %78 = icmp eq i32 %77, 0
  br i1 %78, label %FloppyPnp.exit, label %bb3.i.i

bb3.i.i:                                          ; preds = %bb2.i.i
  %79 = tail call i32 @__VERIFIER_nondet_int() nounwind
  %80 = icmp eq i32 %79, 1
  br i1 %80, label %FloppyPnp.exit, label %switch_8_default.i.i

switch_8_default.i.i:                             ; preds = %bb3.i.i
  br label %FloppyPnp.exit

FloppyPnp.exit:                                   ; preds = %switch_8_default.i.i, %bb3.i.i, %bb2.i.i, %switch_8_default.i9.i, %bb3.i8.i, %bb2.i7.i, %switch_8_default.i28.i, %bb3.i27.i, %bb2.i26.i, %bb31.i, %bb30.i, %switch_8_default.i76.i, %bb3.i75.i, %bb2.i74.i, %switch_8_default.i98.i, %bb3.i97.i, %bb2.i96.i, %FlQueueIrpToThread.exit.i, %bb13.i, %switch_8_default.i133.i, %bb3.i132.i, %bb2.i131.i, %bb13.i158.i, %while_1_break.i.i, %FlFdcDeviceIo.exit.i.i, %bb6.i152.i, %switch_2_3
  %s.0 = phi i32 [ 4, %switch_8_default.i133.i ], [ 4, %switch_8_default.i98.i ], [ 4, %switch_8_default.i76.i ], [ 4, %switch_8_default.i28.i ], [ 4, %switch_8_default.i.i ], [ 4, %switch_8_default.i9.i ], [ 2, %switch_2_3 ], [ 2, %while_1_break.i.i ], [ 2, %FlFdcDeviceIo.exit.i.i ], [ 2, %bb6.i152.i ], [ 2, %bb13.i158.i ], [ 4, %bb2.i131.i ], [ 4, %bb3.i132.i ], [ 2, %bb13.i ], [ 2, %FlQueueIrpToThread.exit.i ], [ 4, %bb2.i96.i ], [ 4, %bb3.i97.i ], [ 4, %bb2.i74.i ], [ 4, %bb3.i75.i ], [ 2, %bb30.i ], [ 2, %bb31.i ], [ 4, %bb2.i26.i ], [ 4, %bb3.i27.i ], [ 4, %bb2.i7.i ], [ 4, %bb3.i8.i ], [ 4, %bb2.i.i ], [ 4, %bb3.i.i ]
  %pended.2 = phi i32 [ 0, %switch_8_default.i133.i ], [ %pended.0.reg2mem.0, %switch_8_default.i98.i ], [ 0, %switch_8_default.i76.i ], [ 0, %switch_8_default.i28.i ], [ 0, %switch_8_default.i.i ], [ 0, %switch_8_default.i9.i ], [ 0, %switch_2_3 ], [ 0, %while_1_break.i.i ], [ 0, %FlFdcDeviceIo.exit.i.i ], [ 0, %bb6.i152.i ], [ 0, %bb13.i158.i ], [ 0, %bb2.i131.i ], [ 0, %bb3.i132.i ], [ 0, %bb13.i ], [ 0, %FlQueueIrpToThread.exit.i ], [ %pended.0.reg2mem.0, %bb2.i96.i ], [ %pended.0.reg2mem.0, %bb3.i97.i ], [ 0, %bb2.i74.i ], [ 0, %bb3.i75.i ], [ 0, %bb30.i ], [ 0, %bb31.i ], [ 0, %bb2.i26.i ], [ 0, %bb3.i27.i ], [ 0, %bb2.i7.i ], [ 0, %bb3.i8.i ], [ 0, %bb2.i.i ], [ 0, %bb3.i.i ]
  %lowerDriverReturn.2 = phi i32 [ 259, %switch_8_default.i133.i ], [ 259, %switch_8_default.i98.i ], [ 259, %switch_8_default.i76.i ], [ 259, %switch_8_default.i28.i ], [ 259, %switch_8_default.i.i ], [ 259, %switch_8_default.i9.i ], [ 0, %switch_2_3 ], [ %lowerDriverReturn.5, %bb13.i158.i ], [ %returnVal2.0.i.i.i.reg2mem.1, %bb6.i152.i ], [ %lowerDriverReturn.5, %FlFdcDeviceIo.exit.i.i ], [ %lowerDriverReturn.5, %while_1_break.i.i ], [ 0, %bb2.i131.i ], [ -1073741823, %bb3.i132.i ], [ 0, %bb13.i ], [ 0, %FlQueueIrpToThread.exit.i ], [ 0, %bb2.i96.i ], [ -1073741823, %bb3.i97.i ], [ 0, %bb2.i74.i ], [ -1073741823, %bb3.i75.i ], [ %returnVal2.0.i57.i.reg2mem.0, %bb30.i ], [ %returnVal2.0.i57.i.reg2mem.1, %bb31.i ], [ 0, %bb2.i26.i ], [ -1073741823, %bb3.i27.i ], [ 0, %bb2.i7.i ], [ -1073741823, %bb3.i8.i ], [ 0, %bb2.i.i ], [ -1073741823, %bb3.i.i ]
  %81 = phi i32 [ 259, %switch_8_default.i133.i ], [ 259, %switch_8_default.i98.i ], [ 259, %switch_8_default.i76.i ], [ 259, %switch_8_default.i28.i ], [ 259, %switch_8_default.i.i ], [ 259, %switch_8_default.i9.i ], [ -1073741738, %switch_2_3 ], [ %ntStatus.0.i.i.reg2mem.0, %bb13.i158.i ], [ -1073741670, %bb6.i152.i ], [ %33, %FlFdcDeviceIo.exit.i.i ], [ %33, %while_1_break.i.i ], [ 0, %bb2.i131.i ], [ -1073741823, %bb3.i132.i ], [ -1073741823, %bb13.i ], [ -1073741823, %FlQueueIrpToThread.exit.i ], [ 0, %bb2.i96.i ], [ -1073741823, %bb3.i97.i ], [ 0, %bb2.i74.i ], [ -1073741823, %bb3.i75.i ], [ 0, %bb30.i ], [ %ntStatus.3.i, %bb31.i ], [ 0, %bb2.i26.i ], [ -1073741823, %bb3.i27.i ], [ 0, %bb2.i7.i ], [ -1073741823, %bb3.i8.i ], [ 0, %bb2.i.i ], [ -1073741823, %bb3.i.i ]
  %82 = icmp eq i32 %pended.2, 1
  %83 = icmp eq i32 %s.0, 1
  %or.cond21 = and i1 %82, %83
  br i1 %or.cond21, label %__UFO__2, label %_L___2

__UFO__1:                                         ; preds = %__UFO__1, %entry
  br label %__UFO__1

_L___2:                                           ; preds = %FloppyPnp.exit
  %84 = icmp eq i32 %s.0, 6
  %or.cond22 = and i1 %82, %84
  br i1 %or.cond22, label %__UFO__2, label %_L___1

_L___1:                                           ; preds = %_L___2
  %85 = icmp eq i32 %s.0, 0
  %86 = icmp eq i32 %81, -1
  %or.cond = or i1 %86, %85
  br i1 %or.cond, label %__UFO__2, label %NodeBlock89

NodeBlock89:                                      ; preds = %_L___1
  %Pivot90 = icmp ult i32 %s.0, 4
  br i1 %Pivot90, label %LeafBlock81, label %LeafBlock83

LeafBlock83:                                      ; preds = %NodeBlock89
  %SwitchLeaf84 = icmp eq i32 %s.0, 4
  br i1 %SwitchLeaf84, label %_L___0, label %UnifiedReturnBlock

LeafBlock81:                                      ; preds = %NodeBlock89
  %SwitchLeaf82 = icmp eq i32 %s.0, 2
  br i1 %SwitchLeaf82, label %_L___0, label %UnifiedReturnBlock

_L___0:                                           ; preds = %LeafBlock81, %LeafBlock83
  br i1 %82, label %bb14, label %bb17

bb14:                                             ; preds = %_L___0
  %87 = icmp eq i32 %81, 259
  br i1 %87, label %__UFO__2, label %UnifiedReturnBlock

bb17:                                             ; preds = %_L___0
  %88 = icmp eq i32 %s.0, 2
  br i1 %88, label %bb18, label %bb21

bb18:                                             ; preds = %bb17
  %89 = icmp eq i32 %81, 259
  br i1 %89, label %UnifiedReturnBlock, label %__UFO__2

bb21:                                             ; preds = %bb17
  %90 = icmp eq i32 %81, %lowerDriverReturn.2
  br i1 %90, label %__UFO__2, label %UnifiedReturnBlock

__UFO__2:                                         ; preds = %__UFO__2, %bb21, %bb18, %bb14, %_L___1, %_L___2, %FloppyPnp.exit
  br label %__UFO__2

UnifiedReturnBlock:                               ; preds = %bb21, %bb18, %bb14, %LeafBlock81, %LeafBlock83, %bb31.i
  ret i32 42
}

declare i32 @ufo.nondet.1()

declare i1 @ufo.nondet.2()
