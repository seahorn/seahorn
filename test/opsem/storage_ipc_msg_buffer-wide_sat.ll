; RUN: %seafatbmc -m32 -O0 --inline --horn-bv2-ptr-size=4 --horn-bv2-word-size=4 "%s" 2>&1 | %oc %s
; CHECK: ^sat$
; ModuleID = 'llvm-link'
source_filename = "llvm-link"
target datalayout = "e-m:e-p:32:32-Fi8-i64:64-v128:64:128-a:0:32-n32-S64"
target triple = "thumbv8-unknown-linux-gnu"

%struct.ipc_port_context = type { %struct.ipc_context, %struct.ipc_port_ops, %struct.list_node }
%struct.ipc_context = type { void (%struct.ipc_context*, %struct.uevent*)*, i32 }
%struct.uevent = type { i32, i32, i8* }
%struct.ipc_port_ops = type { %struct.ipc_channel_context* (%struct.ipc_port_context*, %struct.uuid*, i32)* }
%struct.ipc_channel_context = type { %struct.ipc_context, %struct.ipc_channel_ops, %struct.list_node }
%struct.ipc_channel_ops = type { i32 (%struct.ipc_channel_context*, i8*, i32)*, void (%struct.ipc_channel_context*)* }
%struct.uuid = type { i32, i16, i16, [8 x i8] }
%struct.list_node = type { %struct.list_node*, %struct.list_node* }
%struct._IO_FILE = type opaque
%struct.handle_table = type { i32, i8, i8*, i32, i8, i8*, i32, i8, i8* }
%struct.iovec = type { i8*, i32 }
%struct.ipc_msg = type { i32, %struct.iovec*, i32, i32* }
%struct.ipc_msg_info = type { i32, i32, i32 }

@__const.main.ctx = private unnamed_addr constant %struct.ipc_port_context { %struct.ipc_context zeroinitializer, %struct.ipc_port_ops { %struct.ipc_channel_context* (%struct.ipc_port_context*, %struct.uuid*, i32)* @sea_channel_connect }, %struct.list_node zeroinitializer }, align 4
@.str = private unnamed_addr constant [33 x i8] c"com.android.trusty.storage.proxy\00", align 1
@stderr = external dso_local constant %struct._IO_FILE*, align 4
@.str.1 = private unnamed_addr constant [38 x i8] c"%s: %d: %s: failed (%ld) to send_msg\0A\00", align 1
@.str.1.2 = private unnamed_addr constant [7 x i8] c"ss-ipc\00", align 1
@__func__.sync_ipc_send_msg = private unnamed_addr constant [18 x i8] c"sync_ipc_send_msg\00", align 1
@.str.2 = private unnamed_addr constant [20 x i8] c"rx_iovec_count == 0\00", align 1
@.str.3 = private unnamed_addr constant [91 x i8] c"/home/s2priya/seahorn/verify-trusty/verifyTrusty/seahorn/jobs/storage_ipc_msg_buffer/ipc.c\00", align 1
@.str.4 = private unnamed_addr constant [18 x i8] c"rx_iovecs == NULL\00", align 1
@.str.5 = private unnamed_addr constant [44 x i8] c"%s: %d: %s: failed (%ld) to await response\0A\00", align 1
@.str.6 = private unnamed_addr constant [43 x i8] c"%s: %d: %s: invalid response length (%zu)\0A\00", align 1
@.str.7 = private unnamed_addr constant [52 x i8] c"%s: %d: %s: response buffer too short (%zu < %zu) \0A\00", align 1
@.str.8 = private unnamed_addr constant [38 x i8] c"%s: %d: %s: response has error (%ld)\0A\00", align 1
@.str.25 = private unnamed_addr constant [38 x i8] c"%s: %d: %s: failed to read msg (%ld)\0A\00", align 1
@__func__.read_response = private unnamed_addr constant [14 x i8] c"read_response\00", align 1
@.str.23 = private unnamed_addr constant [51 x i8] c"%s: %d: %s: interrupted waiting for response (%ld)\00", align 1
@__func__.await_response = private unnamed_addr constant [15 x i8] c"await_response\00", align 1
@.str.24 = private unnamed_addr constant [37 x i8] c"%s: %d: %s: failed to get_msg (%ld)\0A\00", align 1
@.str.22 = private unnamed_addr constant [54 x i8] c"%s: %d: failed to wait for outgoing queue to free up\0A\00", align 1
@.str.9 = private unnamed_addr constant [3 x i8] c"ev\00", align 1
@__func__.dispatch_event = private unnamed_addr constant [15 x i8] c"dispatch_event\00", align 1
@.str.10 = private unnamed_addr constant [8 x i8] c"context\00", align 1
@.str.11 = private unnamed_addr constant [21 x i8] c"context->evt_handler\00", align 1
@.str.12 = private unnamed_addr constant [30 x i8] c"context->handle == ev->handle\00", align 1
@.str.13 = private unnamed_addr constant [5 x i8] c"ctxp\00", align 1
@__func__.ipc_port_create = private unnamed_addr constant [16 x i8] c"ipc_port_create\00", align 1
@.str.14 = private unnamed_addr constant [30 x i8] c"is_valid_port_ops(&ctxp->ops)\00", align 1
@.str.15 = private unnamed_addr constant [37 x i8] c"%s: %d: Failed to create port %s %d\0A\00", align 1
@.str.16 = private unnamed_addr constant [46 x i8] c"%s: %d: Failed to set cookie on port %s (%d)\0A\00", align 1
@.str.17 = private unnamed_addr constant [54 x i8] c"%s: %d: Failed to create msg buffer of size %zu (%d)\0A\00", align 1
@.str.26 = private unnamed_addr constant [34 x i8] c"is_valid_port_ops(&port_ctx->ops)\00", align 1
@__func__.handle_port = private unnamed_addr constant [12 x i8] c"handle_port\00", align 1
@.str.28 = private unnamed_addr constant [42 x i8] c"%s: %d: failed (%d) to accept on port %d\0A\00", align 1
@.str.29 = private unnamed_addr constant [53 x i8] c"%s: %d: %s: failure initializing channel state (%d)\0A\00", align 1
@__func__.do_connect = private unnamed_addr constant [11 x i8] c"do_connect\00", align 1
@.str.30 = private unnamed_addr constant [34 x i8] c"is_valid_chan_ops(&chan_ctx->ops)\00", align 1
@.str.31 = private unnamed_addr constant [46 x i8] c"%s: %d: failed (%d) to set_cookie on chan %d\0A\00", align 1
@.str.32 = private unnamed_addr constant [37 x i8] c"is_valid_chan_ops(&channel_ctx->ops)\00", align 1
@__func__.handle_channel = private unnamed_addr constant [15 x i8] c"handle_channel\00", align 1
@.str.33 = private unnamed_addr constant [51 x i8] c"%s: %d: error (%d) in channel, disconnecting peer\0A\00", align 1
@.str.34 = private unnamed_addr constant [63 x i8] c"%s: %d: error: unexpected message in channel (%d). closing...\0A\00", align 1
@.str.36 = private unnamed_addr constant [66 x i8] c"%s: %d: failed (%d) to get_msg for chan (%d), closing connection\0A\00", align 1
@.str.37 = private unnamed_addr constant [35 x i8] c"%s: %d: %s: message too large %zu\0A\00", align 1
@__func__.do_handle_msg = private unnamed_addr constant [14 x i8] c"do_handle_msg\00", align 1
@msg_buf = internal global i8* null, align 4, !dbg !0
@.str.38 = private unnamed_addr constant [37 x i8] c"%s: %d: failed to read msg (%d, %d)\0A\00", align 1
@.str.39 = private unnamed_addr constant [42 x i8] c"%s: %d: invalid message of size (%d, %d)\0A\00", align 1
@.str.35 = private unnamed_addr constant [42 x i8] c"%s: %d: error event (0x%x) for chan (%d)\0A\00", align 1
@__func__.to_channel_context = private unnamed_addr constant [19 x i8] c"to_channel_context\00", align 1
@.str.27 = private unnamed_addr constant [42 x i8] c"%s: %d: error event (0x%x) for port (%d)\0A\00", align 1
@__func__.to_port_context = private unnamed_addr constant [16 x i8] c"to_port_context\00", align 1
@msg_buf_size = internal global i32 0, align 4, !dbg !152
@.str.18 = private unnamed_addr constant [9 x i8] c"chan_ctx\00", align 1
@__func__.ipc_port_destroy = private unnamed_addr constant [17 x i8] c"ipc_port_destroy\00", align 1
@.str.19 = private unnamed_addr constant [43 x i8] c"%s: %d: client still connected, handle %d\0A\00", align 1
@.str.20 = private unnamed_addr constant [28 x i8] c"%s: %d: invalid access: %d\0A\00", align 1
@.str.21 = private unnamed_addr constant [30 x i8] c"%s: %d: wait_any failed (%d)\0A\00", align 1
@cur_msg_id = internal global i32 0, align 4, !dbg !155
@cur_msg_retired = internal global i8 1, align 1, !dbg !217
@ht = internal global %struct.handle_table zeroinitializer, align 4, !dbg !219

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @main() #0 !dbg !346 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.ipc_port_context, align 4
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca %struct.uevent, align 4
  %6 = alloca %struct.uevent, align 4
  store i32 0, i32* %1, align 4
  call arm_aapcscc void @handle_table_init(i32 -1, i32 -1, i32 -1), !dbg !353
  %7 = bitcast %struct.ipc_port_context* %2 to i8*, !dbg !354
  call void @llvm.lifetime.start.p0i8(i64 20, i8* %7) #6, !dbg !354
  call void @llvm.dbg.declare(metadata %struct.ipc_port_context* %2, metadata !348, metadata !DIExpression()), !dbg !355
  %8 = bitcast %struct.ipc_port_context* %2 to i8*, !dbg !355
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* align 4 %8, i8* align 4 bitcast (%struct.ipc_port_context* @__const.main.ctx to i8*), i32 20, i1 false), !dbg !355
  %9 = bitcast i32* %3 to i8*, !dbg !356
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %9) #6, !dbg !356
  call void @llvm.dbg.declare(metadata i32* %3, metadata !349, metadata !DIExpression()), !dbg !357
  %10 = call arm_aapcscc i32 @ipc_port_create(%struct.ipc_port_context* %2, i8* getelementptr inbounds ([33 x i8], [33 x i8]* @.str, i32 0, i32 0), i32 1, i32 4096, i32 3), !dbg !358
  store i32 %10, i32* %3, align 4, !dbg !357, !tbaa !359
  %11 = load i32, i32* %3, align 4, !dbg !363, !tbaa !359
  %12 = icmp slt i32 %11, 0, !dbg !365
  br i1 %12, label %13, label %15, !dbg !366

13:                                               ; preds = %0
  %14 = load i32, i32* %3, align 4, !dbg !367, !tbaa !359
  store i32 %14, i32* %1, align 4, !dbg !369
  store i32 1, i32* %4, align 4
  br label %49, !dbg !369

15:                                               ; preds = %0
  %16 = bitcast %struct.uevent* %5 to i8*, !dbg !370
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %16) #6, !dbg !370
  call void @llvm.dbg.declare(metadata %struct.uevent* %5, metadata !350, metadata !DIExpression()), !dbg !371
  %17 = getelementptr inbounds %struct.uevent, %struct.uevent* %5, i32 0, i32 0, !dbg !372
  store i32 -1, i32* %17, align 4, !dbg !373, !tbaa !374
  %18 = getelementptr inbounds %struct.uevent, %struct.uevent* %5, i32 0, i32 1, !dbg !377
  store i32 0, i32* %18, align 4, !dbg !378, !tbaa !379
  %19 = getelementptr inbounds %struct.uevent, %struct.uevent* %5, i32 0, i32 2, !dbg !380
  store i8* null, i8** %19, align 4, !dbg !381, !tbaa !382
  %20 = call arm_aapcscc i32 @wait_any(%struct.uevent* %5, i32 -1), !dbg !383
  store i32 %20, i32* %3, align 4, !dbg !384, !tbaa !359
  %21 = load i32, i32* %3, align 4, !dbg !385, !tbaa !359
  %22 = icmp slt i32 %21, 0, !dbg !387
  br i1 %22, label %23, label %25, !dbg !388

23:                                               ; preds = %15
  %24 = load i32, i32* %3, align 4, !dbg !389, !tbaa !359
  store i32 %24, i32* %1, align 4, !dbg !391
  store i32 1, i32* %4, align 4
  br label %47, !dbg !391

25:                                               ; preds = %15
  %26 = load i32, i32* %3, align 4, !dbg !392, !tbaa !359
  %27 = icmp eq i32 %26, 0, !dbg !394
  br i1 %27, label %28, label %29, !dbg !395

28:                                               ; preds = %25
  call arm_aapcscc void @dispatch_event(%struct.uevent* %5), !dbg !396
  br label %29, !dbg !398

29:                                               ; preds = %28, %25
  %30 = bitcast %struct.uevent* %6 to i8*, !dbg !399
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %30) #6, !dbg !399
  call void @llvm.dbg.declare(metadata %struct.uevent* %6, metadata !352, metadata !DIExpression()), !dbg !400
  %31 = getelementptr inbounds %struct.uevent, %struct.uevent* %6, i32 0, i32 0, !dbg !401
  store i32 -1, i32* %31, align 4, !dbg !402, !tbaa !374
  %32 = getelementptr inbounds %struct.uevent, %struct.uevent* %6, i32 0, i32 1, !dbg !403
  store i32 0, i32* %32, align 4, !dbg !404, !tbaa !379
  %33 = getelementptr inbounds %struct.uevent, %struct.uevent* %6, i32 0, i32 2, !dbg !405
  store i8* null, i8** %33, align 4, !dbg !406, !tbaa !382
  %34 = call arm_aapcscc i32 @wait_any(%struct.uevent* %6, i32 -1), !dbg !407
  store i32 %34, i32* %3, align 4, !dbg !408, !tbaa !359
  %35 = load i32, i32* %3, align 4, !dbg !409, !tbaa !359
  %36 = icmp slt i32 %35, 0, !dbg !411
  br i1 %36, label %37, label %39, !dbg !412

37:                                               ; preds = %29
  %38 = load i32, i32* %3, align 4, !dbg !413, !tbaa !359
  store i32 %38, i32* %1, align 4, !dbg !415
  store i32 1, i32* %4, align 4
  br label %45, !dbg !415

39:                                               ; preds = %29
  %40 = load i32, i32* %3, align 4, !dbg !416, !tbaa !359
  %41 = icmp eq i32 %40, 0, !dbg !418
  br i1 %41, label %42, label %43, !dbg !419

42:                                               ; preds = %39
  call arm_aapcscc void @dispatch_event(%struct.uevent* %6), !dbg !420
  br label %43, !dbg !422

43:                                               ; preds = %42, %39
  %44 = call arm_aapcscc i32 @ipc_port_destroy(%struct.ipc_port_context* %2), !dbg !423
  store i32 0, i32* %1, align 4, !dbg !424
  store i32 1, i32* %4, align 4
  br label %45, !dbg !424

45:                                               ; preds = %43, %37
  %46 = bitcast %struct.uevent* %6 to i8*, !dbg !425
  call void @llvm.lifetime.end.p0i8(i64 12, i8* %46) #6, !dbg !425
  br label %47

47:                                               ; preds = %45, %23
  %48 = bitcast %struct.uevent* %5 to i8*, !dbg !425
  call void @llvm.lifetime.end.p0i8(i64 12, i8* %48) #6, !dbg !425
  br label %49

49:                                               ; preds = %47, %13
  %50 = bitcast i32* %3 to i8*, !dbg !425
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %50) #6, !dbg !425
  %51 = bitcast %struct.ipc_port_context* %2 to i8*, !dbg !425
  call void @llvm.lifetime.end.p0i8(i64 20, i8* %51) #6, !dbg !425
  %52 = load i32, i32* %1, align 4, !dbg !425
  ret i32 %52, !dbg !425
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.start.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #2

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memcpy.p0i8.p0i8.i32(i8* noalias nocapture writeonly, i8* noalias nocapture readonly, i32, i1 immarg) #1

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.lifetime.end.p0i8(i64 immarg, i8* nocapture) #1

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc %struct.ipc_channel_context* @sea_channel_connect(%struct.ipc_port_context* %0, %struct.uuid* %1, i32 %2) #0 !dbg !426 {
  %4 = alloca %struct.ipc_port_context*, align 4
  %5 = alloca %struct.uuid*, align 4
  %6 = alloca i32, align 4
  %7 = alloca %struct.ipc_channel_context*, align 4
  store %struct.ipc_port_context* %0, %struct.ipc_port_context** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_port_context** %4, metadata !428, metadata !DIExpression()), !dbg !433
  store %struct.uuid* %1, %struct.uuid** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uuid** %5, metadata !429, metadata !DIExpression()), !dbg !434
  store i32 %2, i32* %6, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %6, metadata !430, metadata !DIExpression()), !dbg !435
  %8 = bitcast %struct.ipc_channel_context** %7 to i8*, !dbg !436
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %8) #6, !dbg !436
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %7, metadata !431, metadata !DIExpression()), !dbg !437
  %9 = call arm_aapcscc i8* @malloc(i32 24), !dbg !438
  %10 = bitcast i8* %9 to %struct.ipc_channel_context*, !dbg !438
  store %struct.ipc_channel_context* %10, %struct.ipc_channel_context** %7, align 4, !dbg !437, !tbaa !432
  %11 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %7, align 4, !dbg !439, !tbaa !432
  %12 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %11, i32 0, i32 1, !dbg !440
  %13 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %12, i32 0, i32 1, !dbg !441
  store void (%struct.ipc_channel_context*)* @sea_ipc_disconnect_handler, void (%struct.ipc_channel_context*)** %13, align 4, !dbg !442, !tbaa !443
  %14 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %7, align 4, !dbg !448, !tbaa !432
  %15 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %14, i32 0, i32 1, !dbg !449
  %16 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %15, i32 0, i32 0, !dbg !450
  store i32 (%struct.ipc_channel_context*, i8*, i32)* @sea_ipc_msg_handler, i32 (%struct.ipc_channel_context*, i8*, i32)** %16, align 4, !dbg !451, !tbaa !452
  %17 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %7, align 4, !dbg !453, !tbaa !432
  %18 = bitcast %struct.ipc_channel_context** %7 to i8*, !dbg !454
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %18) #6, !dbg !454
  ret %struct.ipc_channel_context* %17, !dbg !455
}

declare dso_local arm_aapcscc i8* @malloc(i32) #3

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc void @sea_ipc_disconnect_handler(%struct.ipc_channel_context* %0) #0 !dbg !456 {
  %2 = alloca %struct.ipc_channel_context*, align 4
  store %struct.ipc_channel_context* %0, %struct.ipc_channel_context** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %2, metadata !458, metadata !DIExpression()), !dbg !459
  %3 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %2, align 4, !dbg !460, !tbaa !432
  %4 = icmp ne %struct.ipc_channel_context* %3, null, !dbg !460
  br i1 %4, label %5, label %8, !dbg !462

5:                                                ; preds = %1
  %6 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %2, align 4, !dbg !463, !tbaa !432
  %7 = bitcast %struct.ipc_channel_context* %6 to i8*, !dbg !463
  call arm_aapcscc void @free(i8* %7), !dbg !464
  br label %8, !dbg !464

8:                                                ; preds = %5, %1
  ret void, !dbg !465
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @sea_ipc_msg_handler(%struct.ipc_channel_context* %0, i8* %1, i32 %2) #0 !dbg !466 {
  %4 = alloca i32, align 4
  %5 = alloca %struct.ipc_channel_context*, align 4
  %6 = alloca i8*, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.iovec, align 4
  %9 = alloca %struct.ipc_msg, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  store %struct.ipc_channel_context* %0, %struct.ipc_channel_context** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %5, metadata !468, metadata !DIExpression()), !dbg !475
  store i8* %1, i8** %6, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata i8** %6, metadata !469, metadata !DIExpression()), !dbg !476
  store i32 %2, i32* %7, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %7, metadata !470, metadata !DIExpression()), !dbg !477
  %12 = bitcast %struct.iovec* %8 to i8*, !dbg !478
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %12) #6, !dbg !478
  call void @llvm.dbg.declare(metadata %struct.iovec* %8, metadata !471, metadata !DIExpression()), !dbg !479
  %13 = getelementptr inbounds %struct.iovec, %struct.iovec* %8, i32 0, i32 0, !dbg !480
  %14 = load i8*, i8** %6, align 4, !dbg !481, !tbaa !432
  store i8* %14, i8** %13, align 4, !dbg !480, !tbaa !482
  %15 = getelementptr inbounds %struct.iovec, %struct.iovec* %8, i32 0, i32 1, !dbg !480
  %16 = load i32, i32* %7, align 4, !dbg !484, !tbaa !359
  store i32 %16, i32* %15, align 4, !dbg !480, !tbaa !485
  %17 = bitcast %struct.ipc_msg* %9 to i8*, !dbg !486
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %17) #6, !dbg !486
  call void @llvm.dbg.declare(metadata %struct.ipc_msg* %9, metadata !472, metadata !DIExpression()), !dbg !487
  %18 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %9, i32 0, i32 0, !dbg !488
  store i32 1, i32* %18, align 4, !dbg !488, !tbaa !489
  %19 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %9, i32 0, i32 1, !dbg !488
  store %struct.iovec* %8, %struct.iovec** %19, align 4, !dbg !488, !tbaa !491
  %20 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %9, i32 0, i32 2, !dbg !488
  store i32 0, i32* %20, align 4, !dbg !488, !tbaa !492
  %21 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %9, i32 0, i32 3, !dbg !488
  store i32* null, i32** %21, align 4, !dbg !488, !tbaa !493
  %22 = bitcast i32* %10 to i8*, !dbg !494
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %22) #6, !dbg !494
  call void @llvm.dbg.declare(metadata i32* %10, metadata !474, metadata !DIExpression()), !dbg !495
  %23 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !496, !tbaa !432
  %24 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %23, i32 0, i32 0, !dbg !497
  %25 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %24, i32 0, i32 1, !dbg !498
  %26 = load i32, i32* %25, align 4, !dbg !498, !tbaa !499
  %27 = call arm_aapcscc i32 @send_msg(i32 %26, %struct.ipc_msg* %9), !dbg !500
  store i32 %27, i32* %10, align 4, !dbg !495, !tbaa !359
  %28 = load i32, i32* %10, align 4, !dbg !501, !tbaa !359
  %29 = icmp slt i32 %28, 0, !dbg !503
  br i1 %29, label %30, label %32, !dbg !504

30:                                               ; preds = %3
  %31 = load i32, i32* %10, align 4, !dbg !505, !tbaa !359
  store i32 %31, i32* %4, align 4, !dbg !507
  store i32 1, i32* %11, align 4
  br label %33, !dbg !507

32:                                               ; preds = %3
  store i32 0, i32* %4, align 4, !dbg !508
  store i32 1, i32* %11, align 4
  br label %33, !dbg !508

33:                                               ; preds = %32, %30
  %34 = bitcast i32* %10 to i8*, !dbg !509
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %34) #6, !dbg !509
  %35 = bitcast %struct.ipc_msg* %9 to i8*, !dbg !509
  call void @llvm.lifetime.end.p0i8(i64 16, i8* %35) #6, !dbg !509
  %36 = bitcast %struct.iovec* %8 to i8*, !dbg !509
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %36) #6, !dbg !509
  %37 = load i32, i32* %4, align 4, !dbg !509
  ret i32 %37, !dbg !509
}

declare !dbg !319 dso_local arm_aapcscc void @free(i8*) #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @sync_ipc_send_msg(i32 %0, %struct.iovec* %1, i32 %2, %struct.iovec* %3, i32 %4) #0 !dbg !510 {
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.iovec*, align 4
  %9 = alloca i32, align 4
  %10 = alloca %struct.iovec*, align 4
  %11 = alloca i32, align 4
  %12 = alloca %struct.ipc_msg, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  %15 = alloca %struct.ipc_msg_info, align 4
  %16 = alloca i32, align 4
  %17 = alloca i32, align 4
  %18 = alloca i32, align 4
  %19 = alloca i32, align 4
  store i32 %0, i32* %7, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %7, metadata !514, metadata !DIExpression()), !dbg !528
  store %struct.iovec* %1, %struct.iovec** %8, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.iovec** %8, metadata !515, metadata !DIExpression()), !dbg !529
  store i32 %2, i32* %9, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %9, metadata !516, metadata !DIExpression()), !dbg !530
  store %struct.iovec* %3, %struct.iovec** %10, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.iovec** %10, metadata !517, metadata !DIExpression()), !dbg !531
  store i32 %4, i32* %11, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %11, metadata !518, metadata !DIExpression()), !dbg !532
  %20 = bitcast %struct.ipc_msg* %12 to i8*, !dbg !533
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %20) #6, !dbg !533
  call void @llvm.dbg.declare(metadata %struct.ipc_msg* %12, metadata !519, metadata !DIExpression()), !dbg !534
  %21 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %12, i32 0, i32 0, !dbg !535
  %22 = load i32, i32* %9, align 4, !dbg !536, !tbaa !359
  store i32 %22, i32* %21, align 4, !dbg !535, !tbaa !489
  %23 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %12, i32 0, i32 1, !dbg !535
  %24 = load %struct.iovec*, %struct.iovec** %8, align 4, !dbg !537, !tbaa !432
  store %struct.iovec* %24, %struct.iovec** %23, align 4, !dbg !535, !tbaa !491
  %25 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %12, i32 0, i32 2, !dbg !535
  store i32 0, i32* %25, align 4, !dbg !535, !tbaa !492
  %26 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %12, i32 0, i32 3, !dbg !535
  store i32* null, i32** %26, align 4, !dbg !535, !tbaa !493
  %27 = bitcast i32* %13 to i8*, !dbg !538
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %27) #6, !dbg !538
  call void @llvm.dbg.declare(metadata i32* %13, metadata !520, metadata !DIExpression()), !dbg !539
  %28 = load i32, i32* %7, align 4, !dbg !540, !tbaa !359
  %29 = call arm_aapcscc i32 @send_msg(i32 %28, %struct.ipc_msg* %12), !dbg !541
  store i32 %29, i32* %13, align 4, !dbg !539, !tbaa !542
  %30 = load i32, i32* %13, align 4, !dbg !544, !tbaa !542
  %31 = icmp eq i32 %30, -9, !dbg !546
  br i1 %31, label %32, label %35, !dbg !547

32:                                               ; preds = %5
  %33 = load i32, i32* %7, align 4, !dbg !548, !tbaa !359
  %34 = call arm_aapcscc i32 @wait_to_send(i32 %33, %struct.ipc_msg* %12), !dbg !550
  store i32 %34, i32* %13, align 4, !dbg !551, !tbaa !542
  br label %35, !dbg !552

35:                                               ; preds = %32, %5
  %36 = load i32, i32* %13, align 4, !dbg !553, !tbaa !542
  %37 = icmp slt i32 %36, 0, !dbg !555
  br i1 %37, label %38, label %51, !dbg !556

38:                                               ; preds = %35
  br label %39, !dbg !557

39:                                               ; preds = %38
  br label %40, !dbg !559

40:                                               ; preds = %39
  %41 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !563, !tbaa !432
  %42 = load i32, i32* %13, align 4, !dbg !563, !tbaa !542
  %43 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %41, i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.1, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 305, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %42), !dbg !563
  %44 = load i32, i32* %13, align 4, !dbg !563, !tbaa !542
  %45 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.1, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 305, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %44), !dbg !563
  br label %46, !dbg !563

46:                                               ; preds = %40
  br label %47, !dbg !563

47:                                               ; preds = %46
  br label %48, !dbg !565

48:                                               ; preds = %47
  br label %49, !dbg !565

49:                                               ; preds = %48
  %50 = load i32, i32* %13, align 4, !dbg !566, !tbaa !542
  store i32 %50, i32* %6, align 4, !dbg !567
  store i32 1, i32* %14, align 4
  br label %219, !dbg !567

51:                                               ; preds = %35
  %52 = load %struct.iovec*, %struct.iovec** %10, align 4, !dbg !568, !tbaa !432
  %53 = icmp eq %struct.iovec* %52, null, !dbg !570
  br i1 %53, label %57, label %54, !dbg !571

54:                                               ; preds = %51
  %55 = load i32, i32* %11, align 4, !dbg !572, !tbaa !359
  %56 = icmp eq i32 %55, 0, !dbg !573
  br i1 %56, label %57, label %72, !dbg !574

57:                                               ; preds = %54, %51
  %58 = load i32, i32* %11, align 4, !dbg !575, !tbaa !359
  %59 = icmp eq i32 %58, 0, !dbg !575
  br i1 %59, label %62, label %60, !dbg !575

60:                                               ; preds = %57
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([20 x i8], [20 x i8]* @.str.2, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 310, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0)) #7, !dbg !575
  unreachable, !dbg !575

61:                                               ; No predecessors!
  br label %62, !dbg !575

62:                                               ; preds = %61, %57
  %63 = phi i1 [ true, %57 ], [ false, %61 ]
  %64 = zext i1 %63 to i32, !dbg !575
  %65 = load %struct.iovec*, %struct.iovec** %10, align 4, !dbg !577, !tbaa !432
  %66 = icmp eq %struct.iovec* %65, null, !dbg !577
  br i1 %66, label %69, label %67, !dbg !577

67:                                               ; preds = %62
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([18 x i8], [18 x i8]* @.str.4, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 311, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0)) #7, !dbg !577
  unreachable, !dbg !577

68:                                               ; No predecessors!
  br label %69, !dbg !577

69:                                               ; preds = %68, %62
  %70 = phi i1 [ true, %62 ], [ false, %68 ]
  %71 = zext i1 %70 to i32, !dbg !577
  store i32 0, i32* %6, align 4, !dbg !578
  store i32 1, i32* %14, align 4
  br label %219, !dbg !578

72:                                               ; preds = %54
  %73 = bitcast %struct.ipc_msg_info* %15 to i8*, !dbg !579
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %73) #6, !dbg !579
  call void @llvm.dbg.declare(metadata %struct.ipc_msg_info* %15, metadata !522, metadata !DIExpression()), !dbg !580
  %74 = load i32, i32* %7, align 4, !dbg !581, !tbaa !359
  %75 = call arm_aapcscc i32 @await_response(i32 %74, %struct.ipc_msg_info* %15), !dbg !582
  store i32 %75, i32* %13, align 4, !dbg !583, !tbaa !542
  %76 = load i32, i32* %13, align 4, !dbg !584, !tbaa !542
  %77 = icmp slt i32 %76, 0, !dbg !586
  br i1 %77, label %78, label %91, !dbg !587

78:                                               ; preds = %72
  br label %79, !dbg !588

79:                                               ; preds = %78
  br label %80, !dbg !590

80:                                               ; preds = %79
  %81 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !594, !tbaa !432
  %82 = load i32, i32* %13, align 4, !dbg !594, !tbaa !542
  %83 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %81, i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.5, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 318, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %82), !dbg !594
  %84 = load i32, i32* %13, align 4, !dbg !594, !tbaa !542
  %85 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([44 x i8], [44 x i8]* @.str.5, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 318, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %84), !dbg !594
  br label %86, !dbg !594

86:                                               ; preds = %80
  br label %87, !dbg !594

87:                                               ; preds = %86
  br label %88, !dbg !596

88:                                               ; preds = %87
  br label %89, !dbg !596

89:                                               ; preds = %88
  %90 = load i32, i32* %13, align 4, !dbg !597, !tbaa !542
  store i32 %90, i32* %6, align 4, !dbg !598
  store i32 1, i32* %14, align 4
  br label %217, !dbg !598

91:                                               ; preds = %72
  %92 = bitcast i32* %16 to i8*, !dbg !599
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %92) #6, !dbg !599
  call void @llvm.dbg.declare(metadata i32* %16, metadata !523, metadata !DIExpression()), !dbg !600
  %93 = load %struct.iovec*, %struct.iovec** %10, align 4, !dbg !601, !tbaa !432
  %94 = getelementptr inbounds %struct.iovec, %struct.iovec* %93, i32 0, !dbg !601
  %95 = getelementptr inbounds %struct.iovec, %struct.iovec* %94, i32 0, i32 1, !dbg !602
  %96 = load i32, i32* %95, align 4, !dbg !602, !tbaa !485
  store i32 %96, i32* %16, align 4, !dbg !600, !tbaa !359
  %97 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 0, !dbg !603
  %98 = load i32, i32* %97, align 4, !dbg !603, !tbaa !605
  %99 = load i32, i32* %16, align 4, !dbg !607, !tbaa !359
  %100 = icmp ult i32 %98, %99, !dbg !608
  br i1 %100, label %101, label %119, !dbg !609

101:                                              ; preds = %91
  br label %102, !dbg !610

102:                                              ; preds = %101
  br label %103, !dbg !612

103:                                              ; preds = %102
  %104 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !616, !tbaa !432
  %105 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 0, !dbg !616
  %106 = load i32, i32* %105, align 4, !dbg !616, !tbaa !605
  %107 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %104, i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.6, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 324, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %106), !dbg !616
  %108 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 0, !dbg !616
  %109 = load i32, i32* %108, align 4, !dbg !616, !tbaa !605
  %110 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.6, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 324, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %109), !dbg !616
  br label %111, !dbg !616

111:                                              ; preds = %103
  br label %112, !dbg !616

112:                                              ; preds = %111
  br label %113, !dbg !618

113:                                              ; preds = %112
  br label %114, !dbg !618

114:                                              ; preds = %113
  %115 = load i32, i32* %7, align 4, !dbg !619, !tbaa !359
  %116 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 1, !dbg !620
  %117 = load i32, i32* %116, align 4, !dbg !620, !tbaa !621
  %118 = call arm_aapcscc i32 @put_msg(i32 %115, i32 %117), !dbg !622
  store i32 -7, i32* %6, align 4, !dbg !623
  store i32 1, i32* %14, align 4
  br label %215, !dbg !623

119:                                              ; preds = %91
  %120 = bitcast i32* %17 to i8*, !dbg !624
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %120) #6, !dbg !624
  call void @llvm.dbg.declare(metadata i32* %17, metadata !524, metadata !DIExpression()), !dbg !625
  store i32 0, i32* %17, align 4, !dbg !625, !tbaa !359
  %121 = bitcast i32* %18 to i8*, !dbg !626
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %121) #6, !dbg !626
  call void @llvm.dbg.declare(metadata i32* %18, metadata !525, metadata !DIExpression()), !dbg !627
  store i32 0, i32* %18, align 4, !dbg !627, !tbaa !359
  br label %122, !dbg !626

122:                                              ; preds = %136, %119
  %123 = load i32, i32* %18, align 4, !dbg !628, !tbaa !359
  %124 = load i32, i32* %11, align 4, !dbg !630, !tbaa !359
  %125 = icmp ult i32 %123, %124, !dbg !631
  br i1 %125, label %128, label %126, !dbg !632

126:                                              ; preds = %122
  store i32 14, i32* %14, align 4
  %127 = bitcast i32* %18 to i8*, !dbg !633
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %127) #6, !dbg !633
  br label %139

128:                                              ; preds = %122
  %129 = load %struct.iovec*, %struct.iovec** %10, align 4, !dbg !634, !tbaa !432
  %130 = load i32, i32* %18, align 4, !dbg !636, !tbaa !359
  %131 = getelementptr inbounds %struct.iovec, %struct.iovec* %129, i32 %130, !dbg !634
  %132 = getelementptr inbounds %struct.iovec, %struct.iovec* %131, i32 0, i32 1, !dbg !637
  %133 = load i32, i32* %132, align 4, !dbg !637, !tbaa !485
  %134 = load i32, i32* %17, align 4, !dbg !638, !tbaa !359
  %135 = add i32 %134, %133, !dbg !638
  store i32 %135, i32* %17, align 4, !dbg !638, !tbaa !359
  br label %136, !dbg !639

136:                                              ; preds = %128
  %137 = load i32, i32* %18, align 4, !dbg !640, !tbaa !359
  %138 = add i32 %137, 1, !dbg !640
  store i32 %138, i32* %18, align 4, !dbg !640, !tbaa !359
  br label %122, !dbg !633, !llvm.loop !641

139:                                              ; preds = %126
  %140 = load i32, i32* %17, align 4, !dbg !643, !tbaa !359
  %141 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 0, !dbg !645
  %142 = load i32, i32* %141, align 4, !dbg !645, !tbaa !605
  %143 = icmp ult i32 %140, %142, !dbg !646
  br i1 %143, label %144, label %164, !dbg !647

144:                                              ; preds = %139
  br label %145, !dbg !648

145:                                              ; preds = %144
  br label %146, !dbg !650

146:                                              ; preds = %145
  %147 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !654, !tbaa !432
  %148 = load i32, i32* %17, align 4, !dbg !654, !tbaa !359
  %149 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 0, !dbg !654
  %150 = load i32, i32* %149, align 4, !dbg !654, !tbaa !605
  %151 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %147, i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 337, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %148, i32 %150), !dbg !654
  %152 = load i32, i32* %17, align 4, !dbg !654, !tbaa !359
  %153 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 0, !dbg !654
  %154 = load i32, i32* %153, align 4, !dbg !654, !tbaa !605
  %155 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([52 x i8], [52 x i8]* @.str.7, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 337, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %152, i32 %154), !dbg !654
  br label %156, !dbg !654

156:                                              ; preds = %146
  br label %157, !dbg !654

157:                                              ; preds = %156
  br label %158, !dbg !656

158:                                              ; preds = %157
  br label %159, !dbg !656

159:                                              ; preds = %158
  %160 = load i32, i32* %7, align 4, !dbg !657, !tbaa !359
  %161 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 1, !dbg !658
  %162 = load i32, i32* %161, align 4, !dbg !658, !tbaa !621
  %163 = call arm_aapcscc i32 @put_msg(i32 %160, i32 %162), !dbg !659
  store i32 -32, i32* %6, align 4, !dbg !660
  store i32 1, i32* %14, align 4
  br label %213, !dbg !660

164:                                              ; preds = %139
  %165 = load i32, i32* %7, align 4, !dbg !661, !tbaa !359
  %166 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 1, !dbg !662
  %167 = load i32, i32* %166, align 4, !dbg !662, !tbaa !621
  %168 = load %struct.iovec*, %struct.iovec** %10, align 4, !dbg !663, !tbaa !432
  %169 = load i32, i32* %11, align 4, !dbg !664, !tbaa !359
  %170 = call arm_aapcscc i32 @read_response(i32 %165, i32 %167, %struct.iovec* %168, i32 %169), !dbg !665
  store i32 %170, i32* %13, align 4, !dbg !666, !tbaa !542
  %171 = load i32, i32* %7, align 4, !dbg !667, !tbaa !359
  %172 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 1, !dbg !668
  %173 = load i32, i32* %172, align 4, !dbg !668, !tbaa !621
  %174 = call arm_aapcscc i32 @put_msg(i32 %171, i32 %173), !dbg !669
  %175 = load i32, i32* %13, align 4, !dbg !670, !tbaa !542
  %176 = icmp slt i32 %175, 0, !dbg !672
  br i1 %176, label %177, label %190, !dbg !673

177:                                              ; preds = %164
  br label %178, !dbg !674

178:                                              ; preds = %177
  br label %179, !dbg !676

179:                                              ; preds = %178
  %180 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !680, !tbaa !432
  %181 = load i32, i32* %13, align 4, !dbg !680, !tbaa !542
  %182 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %180, i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.8, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 345, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %181), !dbg !680
  %183 = load i32, i32* %13, align 4, !dbg !680, !tbaa !542
  %184 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.8, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 345, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %183), !dbg !680
  br label %185, !dbg !680

185:                                              ; preds = %179
  br label %186, !dbg !680

186:                                              ; preds = %185
  br label %187, !dbg !682

187:                                              ; preds = %186
  br label %188, !dbg !682

188:                                              ; preds = %187
  %189 = load i32, i32* %13, align 4, !dbg !683, !tbaa !542
  store i32 %189, i32* %6, align 4, !dbg !684
  store i32 1, i32* %14, align 4
  br label %213, !dbg !684

190:                                              ; preds = %164
  %191 = bitcast i32* %19 to i8*, !dbg !685
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %191) #6, !dbg !685
  call void @llvm.dbg.declare(metadata i32* %19, metadata !527, metadata !DIExpression()), !dbg !686
  %192 = load i32, i32* %13, align 4, !dbg !687, !tbaa !542
  store i32 %192, i32* %19, align 4, !dbg !686, !tbaa !359
  %193 = load i32, i32* %19, align 4, !dbg !688, !tbaa !359
  %194 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %15, i32 0, i32 0, !dbg !690
  %195 = load i32, i32* %194, align 4, !dbg !690, !tbaa !605
  %196 = icmp ne i32 %193, %195, !dbg !691
  br i1 %196, label %197, label %209, !dbg !692

197:                                              ; preds = %190
  br label %198, !dbg !693

198:                                              ; preds = %197
  br label %199, !dbg !695

199:                                              ; preds = %198
  %200 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !699, !tbaa !432
  %201 = load i32, i32* %19, align 4, !dbg !699, !tbaa !359
  %202 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %200, i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.6, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 352, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %201), !dbg !699
  %203 = load i32, i32* %19, align 4, !dbg !699, !tbaa !359
  %204 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.6, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 352, i8* getelementptr inbounds ([18 x i8], [18 x i8]* @__func__.sync_ipc_send_msg, i32 0, i32 0), i32 %203), !dbg !699
  br label %205, !dbg !699

205:                                              ; preds = %199
  br label %206, !dbg !699

206:                                              ; preds = %205
  br label %207, !dbg !701

207:                                              ; preds = %206
  br label %208, !dbg !701

208:                                              ; preds = %207
  store i32 -20, i32* %6, align 4, !dbg !702
  store i32 1, i32* %14, align 4
  br label %211, !dbg !702

209:                                              ; preds = %190
  %210 = load i32, i32* %19, align 4, !dbg !703, !tbaa !359
  store i32 %210, i32* %6, align 4, !dbg !704
  store i32 1, i32* %14, align 4
  br label %211, !dbg !704

211:                                              ; preds = %209, %208
  %212 = bitcast i32* %19 to i8*, !dbg !705
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %212) #6, !dbg !705
  br label %213

213:                                              ; preds = %211, %188, %159
  %214 = bitcast i32* %17 to i8*, !dbg !705
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %214) #6, !dbg !705
  br label %215

215:                                              ; preds = %213, %114
  %216 = bitcast i32* %16 to i8*, !dbg !705
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %216) #6, !dbg !705
  br label %217

217:                                              ; preds = %215, %89
  %218 = bitcast %struct.ipc_msg_info* %15 to i8*, !dbg !705
  call void @llvm.lifetime.end.p0i8(i64 12, i8* %218) #6, !dbg !705
  br label %219

219:                                              ; preds = %217, %69, %49
  %220 = bitcast i32* %13 to i8*, !dbg !705
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %220) #6, !dbg !705
  %221 = bitcast %struct.ipc_msg* %12 to i8*, !dbg !705
  call void @llvm.lifetime.end.p0i8(i64 16, i8* %221) #6, !dbg !705
  %222 = load i32, i32* %6, align 4, !dbg !705
  ret i32 %222, !dbg !705
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @wait_to_send(i32 %0, %struct.ipc_msg* %1) #0 !dbg !706 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca %struct.ipc_msg*, align 4
  %6 = alloca i32, align 4
  %7 = alloca %struct.uevent, align 4
  %8 = alloca i32, align 4
  store i32 %0, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !710, metadata !DIExpression()), !dbg !714
  store %struct.ipc_msg* %1, %struct.ipc_msg** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_msg** %5, metadata !711, metadata !DIExpression()), !dbg !715
  %9 = bitcast i32* %6 to i8*, !dbg !716
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %9) #6, !dbg !716
  call void @llvm.dbg.declare(metadata i32* %6, metadata !712, metadata !DIExpression()), !dbg !717
  %10 = bitcast %struct.uevent* %7 to i8*, !dbg !718
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %10) #6, !dbg !718
  call void @llvm.dbg.declare(metadata %struct.uevent* %7, metadata !713, metadata !DIExpression()), !dbg !719
  %11 = bitcast %struct.uevent* %7 to i8*, !dbg !719
  call void @llvm.memset.p0i8.i32(i8* align 4 %11, i8 0, i32 12, i1 false), !dbg !719
  %12 = load i32, i32* %4, align 4, !dbg !720, !tbaa !359
  %13 = call arm_aapcscc i32 @wait(i32 %12, %struct.uevent* %7, i32 -1), !dbg !721
  store i32 %13, i32* %6, align 4, !dbg !722, !tbaa !359
  %14 = load i32, i32* %6, align 4, !dbg !723, !tbaa !359
  %15 = icmp slt i32 %14, 0, !dbg !725
  br i1 %15, label %16, label %27, !dbg !726

16:                                               ; preds = %2
  br label %17, !dbg !727

17:                                               ; preds = %16
  br label %18, !dbg !729

18:                                               ; preds = %17
  %19 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !733, !tbaa !432
  %20 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %19, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.22, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 270), !dbg !733
  %21 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.22, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 270), !dbg !733
  br label %22, !dbg !733

22:                                               ; preds = %18
  br label %23, !dbg !733

23:                                               ; preds = %22
  br label %24, !dbg !735

24:                                               ; preds = %23
  br label %25, !dbg !735

25:                                               ; preds = %24
  %26 = load i32, i32* %6, align 4, !dbg !736, !tbaa !359
  store i32 %26, i32* %3, align 4, !dbg !737
  store i32 1, i32* %8, align 4
  br label %50, !dbg !737

27:                                               ; preds = %2
  %28 = getelementptr inbounds %struct.uevent, %struct.uevent* %7, i32 0, i32 1, !dbg !738
  %29 = load i32, i32* %28, align 4, !dbg !738, !tbaa !379
  %30 = and i32 %29, 16, !dbg !740
  %31 = icmp ne i32 %30, 0, !dbg !740
  br i1 %31, label %32, label %36, !dbg !741

32:                                               ; preds = %27
  %33 = load i32, i32* %4, align 4, !dbg !742, !tbaa !359
  %34 = load %struct.ipc_msg*, %struct.ipc_msg** %5, align 4, !dbg !744, !tbaa !432
  %35 = call arm_aapcscc i32 @send_msg(i32 %33, %struct.ipc_msg* %34), !dbg !745
  store i32 %35, i32* %3, align 4, !dbg !746
  store i32 1, i32* %8, align 4
  br label %50, !dbg !746

36:                                               ; preds = %27
  %37 = getelementptr inbounds %struct.uevent, %struct.uevent* %7, i32 0, i32 1, !dbg !747
  %38 = load i32, i32* %37, align 4, !dbg !747, !tbaa !379
  %39 = and i32 %38, 8, !dbg !749
  %40 = icmp ne i32 %39, 0, !dbg !749
  br i1 %40, label %41, label %42, !dbg !750

41:                                               ; preds = %36
  store i32 -33, i32* %3, align 4, !dbg !751
  store i32 1, i32* %8, align 4
  br label %50, !dbg !751

42:                                               ; preds = %36
  %43 = getelementptr inbounds %struct.uevent, %struct.uevent* %7, i32 0, i32 1, !dbg !753
  %44 = load i32, i32* %43, align 4, !dbg !753, !tbaa !379
  %45 = and i32 %44, 4, !dbg !755
  %46 = icmp ne i32 %45, 0, !dbg !755
  br i1 %46, label %47, label %48, !dbg !756

47:                                               ; preds = %42
  store i32 -15, i32* %3, align 4, !dbg !757
  store i32 1, i32* %8, align 4
  br label %50, !dbg !757

48:                                               ; preds = %42
  %49 = load i32, i32* %6, align 4, !dbg !759, !tbaa !359
  store i32 %49, i32* %3, align 4, !dbg !760
  store i32 1, i32* %8, align 4
  br label %50, !dbg !760

50:                                               ; preds = %48, %47, %41, %32, %25
  %51 = bitcast %struct.uevent* %7 to i8*, !dbg !761
  call void @llvm.lifetime.end.p0i8(i64 12, i8* %51) #6, !dbg !761
  %52 = bitcast i32* %6 to i8*, !dbg !761
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %52) #6, !dbg !761
  %53 = load i32, i32* %3, align 4, !dbg !761
  ret i32 %53, !dbg !761
}

declare dso_local arm_aapcscc i32 @fprintf(%struct._IO_FILE*, i8*, ...) #3

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc i32 @unittest_printf(i8* %0, ...) #4 !dbg !762 {
  %2 = alloca i8*, align 4
  store i8* %0, i8** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata i8** %2, metadata !767, metadata !DIExpression()), !dbg !768
  ret i32 0, !dbg !769
}

; Function Attrs: noreturn
declare dso_local arm_aapcscc void @__assert_fail(i8*, i8*, i32, i8*) #5

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @await_response(i32 %0, %struct.ipc_msg_info* %1) #0 !dbg !770 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca %struct.ipc_msg_info*, align 4
  %6 = alloca %struct.uevent, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  store i32 %0, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !774, metadata !DIExpression()), !dbg !779
  store %struct.ipc_msg_info* %1, %struct.ipc_msg_info** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_msg_info** %5, metadata !775, metadata !DIExpression()), !dbg !780
  %9 = bitcast %struct.uevent* %6 to i8*, !dbg !781
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %9) #6, !dbg !781
  call void @llvm.dbg.declare(metadata %struct.uevent* %6, metadata !776, metadata !DIExpression()), !dbg !782
  %10 = bitcast i32* %7 to i8*, !dbg !783
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %10) #6, !dbg !783
  call void @llvm.dbg.declare(metadata i32* %7, metadata !778, metadata !DIExpression()), !dbg !784
  %11 = load i32, i32* %4, align 4, !dbg !785, !tbaa !359
  %12 = call arm_aapcscc i32 @wait(i32 %11, %struct.uevent* %6, i32 -1), !dbg !786
  store i32 %12, i32* %7, align 4, !dbg !784, !tbaa !542
  %13 = load i32, i32* %7, align 4, !dbg !787, !tbaa !542
  %14 = icmp ne i32 %13, 0, !dbg !789
  br i1 %14, label %15, label %28, !dbg !790

15:                                               ; preds = %2
  br label %16, !dbg !791

16:                                               ; preds = %15
  br label %17, !dbg !793

17:                                               ; preds = %16
  %18 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !797, !tbaa !432
  %19 = load i32, i32* %7, align 4, !dbg !797, !tbaa !542
  %20 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %18, i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.23, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 252, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.await_response, i32 0, i32 0), i32 %19), !dbg !797
  %21 = load i32, i32* %7, align 4, !dbg !797, !tbaa !542
  %22 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.23, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 252, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.await_response, i32 0, i32 0), i32 %21), !dbg !797
  br label %23, !dbg !797

23:                                               ; preds = %17
  br label %24, !dbg !797

24:                                               ; preds = %23
  br label %25, !dbg !799

25:                                               ; preds = %24
  br label %26, !dbg !799

26:                                               ; preds = %25
  %27 = load i32, i32* %7, align 4, !dbg !800, !tbaa !542
  store i32 %27, i32* %3, align 4, !dbg !801
  store i32 1, i32* %8, align 4
  br label %48, !dbg !801

28:                                               ; preds = %2
  %29 = load i32, i32* %4, align 4, !dbg !802, !tbaa !359
  %30 = load %struct.ipc_msg_info*, %struct.ipc_msg_info** %5, align 4, !dbg !803, !tbaa !432
  %31 = call arm_aapcscc i32 @get_msg(i32 %29, %struct.ipc_msg_info* %30), !dbg !804
  store i32 %31, i32* %7, align 4, !dbg !805, !tbaa !542
  %32 = load i32, i32* %7, align 4, !dbg !806, !tbaa !542
  %33 = icmp ne i32 %32, 0, !dbg !808
  br i1 %33, label %34, label %46, !dbg !809

34:                                               ; preds = %28
  br label %35, !dbg !810

35:                                               ; preds = %34
  br label %36, !dbg !812

36:                                               ; preds = %35
  %37 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !816, !tbaa !432
  %38 = load i32, i32* %7, align 4, !dbg !816, !tbaa !542
  %39 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %37, i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.24, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 258, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.await_response, i32 0, i32 0), i32 %38), !dbg !816
  %40 = load i32, i32* %7, align 4, !dbg !816, !tbaa !542
  %41 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.24, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 258, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.await_response, i32 0, i32 0), i32 %40), !dbg !816
  br label %42, !dbg !816

42:                                               ; preds = %36
  br label %43, !dbg !816

43:                                               ; preds = %42
  br label %44, !dbg !818

44:                                               ; preds = %43
  br label %45, !dbg !818

45:                                               ; preds = %44
  br label %46, !dbg !819

46:                                               ; preds = %45, %28
  %47 = load i32, i32* %7, align 4, !dbg !820, !tbaa !542
  store i32 %47, i32* %3, align 4, !dbg !821
  store i32 1, i32* %8, align 4
  br label %48, !dbg !821

48:                                               ; preds = %46, %26
  %49 = bitcast i32* %7 to i8*, !dbg !822
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %49) #6, !dbg !822
  %50 = bitcast %struct.uevent* %6 to i8*, !dbg !822
  call void @llvm.lifetime.end.p0i8(i64 12, i8* %50) #6, !dbg !822
  %51 = load i32, i32* %3, align 4, !dbg !822
  ret i32 %51, !dbg !822
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @read_response(i32 %0, i32 %1, %struct.iovec* %2, i32 %3) #0 !dbg !823 {
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.iovec*, align 4
  %9 = alloca i32, align 4
  %10 = alloca %struct.ipc_msg, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  store i32 %0, i32* %6, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %6, metadata !827, metadata !DIExpression()), !dbg !834
  store i32 %1, i32* %7, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %7, metadata !828, metadata !DIExpression()), !dbg !835
  store %struct.iovec* %2, %struct.iovec** %8, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.iovec** %8, metadata !829, metadata !DIExpression()), !dbg !836
  store i32 %3, i32* %9, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %9, metadata !830, metadata !DIExpression()), !dbg !837
  %14 = bitcast %struct.ipc_msg* %10 to i8*, !dbg !838
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %14) #6, !dbg !838
  call void @llvm.dbg.declare(metadata %struct.ipc_msg* %10, metadata !831, metadata !DIExpression()), !dbg !839
  %15 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %10, i32 0, i32 0, !dbg !840
  %16 = load i32, i32* %9, align 4, !dbg !841, !tbaa !359
  store i32 %16, i32* %15, align 4, !dbg !840, !tbaa !489
  %17 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %10, i32 0, i32 1, !dbg !840
  %18 = load %struct.iovec*, %struct.iovec** %8, align 4, !dbg !842, !tbaa !432
  store %struct.iovec* %18, %struct.iovec** %17, align 4, !dbg !840, !tbaa !491
  %19 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %10, i32 0, i32 2, !dbg !840
  store i32 0, i32* %19, align 4, !dbg !840, !tbaa !492
  %20 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %10, i32 0, i32 3, !dbg !840
  store i32* null, i32** %20, align 4, !dbg !840, !tbaa !493
  %21 = bitcast i32* %11 to i8*, !dbg !843
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %21) #6, !dbg !843
  call void @llvm.dbg.declare(metadata i32* %11, metadata !832, metadata !DIExpression()), !dbg !844
  %22 = load i32, i32* %6, align 4, !dbg !845, !tbaa !359
  %23 = load i32, i32* %7, align 4, !dbg !846, !tbaa !359
  %24 = call arm_aapcscc i32 @read_msg(i32 %22, i32 %23, i32 0, %struct.ipc_msg* %10), !dbg !847
  store i32 %24, i32* %11, align 4, !dbg !844, !tbaa !542
  %25 = load i32, i32* %6, align 4, !dbg !848, !tbaa !359
  %26 = load i32, i32* %7, align 4, !dbg !849, !tbaa !359
  %27 = call arm_aapcscc i32 @put_msg(i32 %25, i32 %26), !dbg !850
  %28 = load i32, i32* %11, align 4, !dbg !851, !tbaa !542
  %29 = icmp slt i32 %28, 0, !dbg !853
  br i1 %29, label %30, label %43, !dbg !854

30:                                               ; preds = %4
  br label %31, !dbg !855

31:                                               ; preds = %30
  br label %32, !dbg !857

32:                                               ; preds = %31
  %33 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !861, !tbaa !432
  %34 = load i32, i32* %11, align 4, !dbg !861, !tbaa !542
  %35 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %33, i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.25, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 240, i8* getelementptr inbounds ([14 x i8], [14 x i8]* @__func__.read_response, i32 0, i32 0), i32 %34), !dbg !861
  %36 = load i32, i32* %11, align 4, !dbg !861, !tbaa !542
  %37 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([38 x i8], [38 x i8]* @.str.25, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 240, i8* getelementptr inbounds ([14 x i8], [14 x i8]* @__func__.read_response, i32 0, i32 0), i32 %36), !dbg !861
  br label %38, !dbg !861

38:                                               ; preds = %32
  br label %39, !dbg !861

39:                                               ; preds = %38
  br label %40, !dbg !863

40:                                               ; preds = %39
  br label %41, !dbg !863

41:                                               ; preds = %40
  %42 = load i32, i32* %11, align 4, !dbg !864, !tbaa !542
  store i32 %42, i32* %5, align 4, !dbg !865
  store i32 1, i32* %12, align 4
  br label %48, !dbg !865

43:                                               ; preds = %4
  %44 = bitcast i32* %13 to i8*, !dbg !866
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %44) #6, !dbg !866
  call void @llvm.dbg.declare(metadata i32* %13, metadata !833, metadata !DIExpression()), !dbg !867
  %45 = load i32, i32* %11, align 4, !dbg !868, !tbaa !542
  store i32 %45, i32* %13, align 4, !dbg !867, !tbaa !359
  %46 = load i32, i32* %13, align 4, !dbg !869, !tbaa !359
  store i32 %46, i32* %5, align 4, !dbg !870
  store i32 1, i32* %12, align 4
  %47 = bitcast i32* %13 to i8*, !dbg !871
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %47) #6, !dbg !871
  br label %48

48:                                               ; preds = %43, %41
  %49 = bitcast i32* %11 to i8*, !dbg !871
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %49) #6, !dbg !871
  %50 = bitcast %struct.ipc_msg* %10 to i8*, !dbg !871
  call void @llvm.lifetime.end.p0i8(i64 16, i8* %50) #6, !dbg !871
  %51 = load i32, i32* %5, align 4, !dbg !871
  ret i32 %51, !dbg !871
}

; Function Attrs: argmemonly nounwind willreturn
declare void @llvm.memset.p0i8.i32(i8* nocapture writeonly, i8, i32, i1 immarg) #1

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc void @dispatch_event(%struct.uevent* %0) #0 !dbg !872 {
  %2 = alloca %struct.uevent*, align 4
  %3 = alloca %struct.ipc_context*, align 4
  store %struct.uevent* %0, %struct.uevent** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %2, metadata !878, metadata !DIExpression()), !dbg !880
  %4 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !881, !tbaa !432
  %5 = icmp ne %struct.uevent* %4, null, !dbg !881
  br i1 %5, label %8, label %6, !dbg !881

6:                                                ; preds = %1
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([3 x i8], [3 x i8]* @.str.9, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 360, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.dispatch_event, i32 0, i32 0)) #7, !dbg !881
  unreachable, !dbg !881

7:                                                ; No predecessors!
  br label %8, !dbg !881

8:                                                ; preds = %7, %1
  %9 = phi i1 [ true, %1 ], [ false, %7 ]
  %10 = zext i1 %9 to i32, !dbg !881
  %11 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !882, !tbaa !432
  %12 = getelementptr inbounds %struct.uevent, %struct.uevent* %11, i32 0, i32 1, !dbg !884
  %13 = load i32, i32* %12, align 4, !dbg !884, !tbaa !379
  %14 = icmp eq i32 %13, 0, !dbg !885
  br i1 %14, label %15, label %16, !dbg !886

15:                                               ; preds = %8
  br label %56, !dbg !887

16:                                               ; preds = %8
  %17 = bitcast %struct.ipc_context** %3 to i8*, !dbg !889
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %17) #6, !dbg !889
  call void @llvm.dbg.declare(metadata %struct.ipc_context** %3, metadata !879, metadata !DIExpression()), !dbg !890
  %18 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !891, !tbaa !432
  %19 = getelementptr inbounds %struct.uevent, %struct.uevent* %18, i32 0, i32 2, !dbg !892
  %20 = load i8*, i8** %19, align 4, !dbg !892, !tbaa !382
  %21 = bitcast i8* %20 to %struct.ipc_context*, !dbg !891
  store %struct.ipc_context* %21, %struct.ipc_context** %3, align 4, !dbg !890, !tbaa !432
  %22 = load %struct.ipc_context*, %struct.ipc_context** %3, align 4, !dbg !893, !tbaa !432
  %23 = icmp ne %struct.ipc_context* %22, null, !dbg !893
  br i1 %23, label %26, label %24, !dbg !893

24:                                               ; preds = %16
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 367, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.dispatch_event, i32 0, i32 0)) #7, !dbg !893
  unreachable, !dbg !893

25:                                               ; No predecessors!
  br label %26, !dbg !893

26:                                               ; preds = %25, %16
  %27 = phi i1 [ true, %16 ], [ false, %25 ]
  %28 = zext i1 %27 to i32, !dbg !893
  %29 = load %struct.ipc_context*, %struct.ipc_context** %3, align 4, !dbg !894, !tbaa !432
  %30 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %29, i32 0, i32 0, !dbg !894
  %31 = load void (%struct.ipc_context*, %struct.uevent*)*, void (%struct.ipc_context*, %struct.uevent*)** %30, align 4, !dbg !894, !tbaa !895
  %32 = icmp ne void (%struct.ipc_context*, %struct.uevent*)* %31, null, !dbg !894
  br i1 %32, label %35, label %33, !dbg !894

33:                                               ; preds = %26
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([21 x i8], [21 x i8]* @.str.11, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 368, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.dispatch_event, i32 0, i32 0)) #7, !dbg !894
  unreachable, !dbg !894

34:                                               ; No predecessors!
  br label %35, !dbg !894

35:                                               ; preds = %34, %26
  %36 = phi i1 [ true, %26 ], [ false, %34 ]
  %37 = zext i1 %36 to i32, !dbg !894
  %38 = load %struct.ipc_context*, %struct.ipc_context** %3, align 4, !dbg !896, !tbaa !432
  %39 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %38, i32 0, i32 1, !dbg !896
  %40 = load i32, i32* %39, align 4, !dbg !896, !tbaa !897
  %41 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !896, !tbaa !432
  %42 = getelementptr inbounds %struct.uevent, %struct.uevent* %41, i32 0, i32 0, !dbg !896
  %43 = load i32, i32* %42, align 4, !dbg !896, !tbaa !374
  %44 = icmp eq i32 %40, %43, !dbg !896
  br i1 %44, label %47, label %45, !dbg !896

45:                                               ; preds = %35
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str.12, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 369, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.dispatch_event, i32 0, i32 0)) #7, !dbg !896
  unreachable, !dbg !896

46:                                               ; No predecessors!
  br label %47, !dbg !896

47:                                               ; preds = %46, %35
  %48 = phi i1 [ true, %35 ], [ false, %46 ]
  %49 = zext i1 %48 to i32, !dbg !896
  %50 = load %struct.ipc_context*, %struct.ipc_context** %3, align 4, !dbg !898, !tbaa !432
  %51 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %50, i32 0, i32 0, !dbg !899
  %52 = load void (%struct.ipc_context*, %struct.uevent*)*, void (%struct.ipc_context*, %struct.uevent*)** %51, align 4, !dbg !899, !tbaa !895
  %53 = load %struct.ipc_context*, %struct.ipc_context** %3, align 4, !dbg !900, !tbaa !432
  %54 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !901, !tbaa !432
  call arm_aapcscc void %52(%struct.ipc_context* %53, %struct.uevent* %54), !dbg !898
  %55 = bitcast %struct.ipc_context** %3 to i8*, !dbg !902
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %55) #6, !dbg !902
  br label %56

56:                                               ; preds = %47, %15
  ret void, !dbg !902
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @ipc_port_create(%struct.ipc_port_context* %0, i8* %1, i32 %2, i32 %3, i32 %4) #0 !dbg !903 {
  %6 = alloca i32, align 4
  %7 = alloca %struct.ipc_port_context*, align 4
  %8 = alloca i8*, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca i32, align 4
  %14 = alloca i32, align 4
  store %struct.ipc_port_context* %0, %struct.ipc_port_context** %7, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_port_context** %7, metadata !907, metadata !DIExpression()), !dbg !916
  store i8* %1, i8** %8, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata i8** %8, metadata !908, metadata !DIExpression()), !dbg !917
  store i32 %2, i32* %9, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %9, metadata !909, metadata !DIExpression()), !dbg !918
  store i32 %3, i32* %10, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %10, metadata !910, metadata !DIExpression()), !dbg !919
  store i32 %4, i32* %11, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %11, metadata !911, metadata !DIExpression()), !dbg !920
  %15 = bitcast i32* %12 to i8*, !dbg !921
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %15) #6, !dbg !921
  call void @llvm.dbg.declare(metadata i32* %12, metadata !912, metadata !DIExpression()), !dbg !922
  %16 = load %struct.ipc_port_context*, %struct.ipc_port_context** %7, align 4, !dbg !923, !tbaa !432
  %17 = icmp ne %struct.ipc_port_context* %16, null, !dbg !923
  br i1 %17, label %20, label %18, !dbg !923

18:                                               ; preds = %5
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @.str.13, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 380, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @__func__.ipc_port_create, i32 0, i32 0)) #7, !dbg !923
  unreachable, !dbg !923

19:                                               ; No predecessors!
  br label %20, !dbg !923

20:                                               ; preds = %19, %5
  %21 = phi i1 [ true, %5 ], [ false, %19 ]
  %22 = zext i1 %21 to i32, !dbg !923
  %23 = load %struct.ipc_port_context*, %struct.ipc_port_context** %7, align 4, !dbg !924, !tbaa !432
  %24 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %23, i32 0, i32 1, !dbg !924
  %25 = call arm_aapcscc i32 @is_valid_port_ops(%struct.ipc_port_ops* %24), !dbg !924
  %26 = icmp ne i32 %25, 0, !dbg !924
  br i1 %26, label %29, label %27, !dbg !924

27:                                               ; preds = %20
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str.14, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 381, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @__func__.ipc_port_create, i32 0, i32 0)) #7, !dbg !924
  unreachable, !dbg !924

28:                                               ; No predecessors!
  br label %29, !dbg !924

29:                                               ; preds = %28, %20
  %30 = phi i1 [ true, %20 ], [ false, %28 ]
  %31 = zext i1 %30 to i32, !dbg !924
  %32 = load i8*, i8** %8, align 4, !dbg !925, !tbaa !432
  %33 = load i32, i32* %9, align 4, !dbg !926, !tbaa !359
  %34 = load i32, i32* %10, align 4, !dbg !927, !tbaa !359
  %35 = load i32, i32* %11, align 4, !dbg !928, !tbaa !359
  %36 = call arm_aapcscc i32 @port_create(i8* %32, i32 %33, i32 %34, i32 %35), !dbg !929
  store i32 %36, i32* %12, align 4, !dbg !930, !tbaa !359
  %37 = load i32, i32* %12, align 4, !dbg !931, !tbaa !359
  %38 = icmp slt i32 %37, 0, !dbg !933
  br i1 %38, label %39, label %54, !dbg !934

39:                                               ; preds = %29
  br label %40, !dbg !935

40:                                               ; preds = %39
  br label %41, !dbg !937

41:                                               ; preds = %40
  %42 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !941, !tbaa !432
  %43 = load i8*, i8** %8, align 4, !dbg !941, !tbaa !432
  %44 = load i32, i32* %12, align 4, !dbg !941, !tbaa !359
  %45 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %42, i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.15, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 386, i8* %43, i32 %44), !dbg !941
  %46 = load i8*, i8** %8, align 4, !dbg !941, !tbaa !432
  %47 = load i32, i32* %12, align 4, !dbg !941, !tbaa !359
  %48 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.15, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 386, i8* %46, i32 %47), !dbg !941
  br label %49, !dbg !941

49:                                               ; preds = %41
  br label %50, !dbg !941

50:                                               ; preds = %49
  br label %51, !dbg !943

51:                                               ; preds = %50
  br label %52, !dbg !943

52:                                               ; preds = %51
  %53 = load i32, i32* %12, align 4, !dbg !944, !tbaa !359
  store i32 %53, i32* %6, align 4, !dbg !945
  store i32 1, i32* %13, align 4
  br label %113, !dbg !945

54:                                               ; preds = %29
  %55 = bitcast i32* %14 to i8*, !dbg !946
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %55) #6, !dbg !946
  call void @llvm.dbg.declare(metadata i32* %14, metadata !913, metadata !DIExpression()), !dbg !947
  %56 = load i32, i32* %12, align 4, !dbg !948, !tbaa !359
  store i32 %56, i32* %14, align 4, !dbg !947, !tbaa !359
  %57 = load i32, i32* %14, align 4, !dbg !949, !tbaa !359
  %58 = load %struct.ipc_port_context*, %struct.ipc_port_context** %7, align 4, !dbg !950, !tbaa !432
  %59 = bitcast %struct.ipc_port_context* %58 to i8*, !dbg !950
  %60 = call arm_aapcscc i32 @set_cookie(i32 %57, i8* %59), !dbg !951
  store i32 %60, i32* %12, align 4, !dbg !952, !tbaa !359
  %61 = load i32, i32* %12, align 4, !dbg !953, !tbaa !359
  %62 = icmp slt i32 %61, 0, !dbg !955
  br i1 %62, label %63, label %77, !dbg !956

63:                                               ; preds = %54
  br label %64, !dbg !957

64:                                               ; preds = %63
  br label %65, !dbg !959

65:                                               ; preds = %64
  %66 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !963, !tbaa !432
  %67 = load i8*, i8** %8, align 4, !dbg !963, !tbaa !432
  %68 = load i32, i32* %12, align 4, !dbg !963, !tbaa !359
  %69 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %66, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.16, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 393, i8* %67, i32 %68), !dbg !963
  %70 = load i8*, i8** %8, align 4, !dbg !963, !tbaa !432
  %71 = load i32, i32* %12, align 4, !dbg !963, !tbaa !359
  %72 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.16, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 393, i8* %70, i32 %71), !dbg !963
  br label %73, !dbg !963

73:                                               ; preds = %65
  br label %74, !dbg !963

74:                                               ; preds = %73
  br label %75, !dbg !965

75:                                               ; preds = %74
  br label %76, !dbg !965

76:                                               ; preds = %75
  br label %106, !dbg !966

77:                                               ; preds = %54
  %78 = load i32, i32* %10, align 4, !dbg !967, !tbaa !359
  %79 = call arm_aapcscc i32 @maybe_grow_msg_buf(i32 %78), !dbg !968
  store i32 %79, i32* %12, align 4, !dbg !969, !tbaa !359
  %80 = load i32, i32* %12, align 4, !dbg !970, !tbaa !359
  %81 = icmp slt i32 %80, 0, !dbg !972
  br i1 %81, label %82, label %96, !dbg !973

82:                                               ; preds = %77
  br label %83, !dbg !974

83:                                               ; preds = %82
  br label %84, !dbg !976

84:                                               ; preds = %83
  %85 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !980, !tbaa !432
  %86 = load i32, i32* %10, align 4, !dbg !980, !tbaa !359
  %87 = load i32, i32* %12, align 4, !dbg !980, !tbaa !359
  %88 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %85, i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.17, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 400, i32 %86, i32 %87), !dbg !980
  %89 = load i32, i32* %10, align 4, !dbg !980, !tbaa !359
  %90 = load i32, i32* %12, align 4, !dbg !980, !tbaa !359
  %91 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([54 x i8], [54 x i8]* @.str.17, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 400, i32 %89, i32 %90), !dbg !980
  br label %92, !dbg !980

92:                                               ; preds = %84
  br label %93, !dbg !980

93:                                               ; preds = %92
  br label %94, !dbg !982

94:                                               ; preds = %93
  br label %95, !dbg !982

95:                                               ; preds = %94
  br label %107, !dbg !983

96:                                               ; preds = %77
  %97 = load i32, i32* %14, align 4, !dbg !984, !tbaa !359
  %98 = load %struct.ipc_port_context*, %struct.ipc_port_context** %7, align 4, !dbg !985, !tbaa !432
  %99 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %98, i32 0, i32 0, !dbg !986
  %100 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %99, i32 0, i32 1, !dbg !987
  store i32 %97, i32* %100, align 4, !dbg !988, !tbaa !989
  %101 = load %struct.ipc_port_context*, %struct.ipc_port_context** %7, align 4, !dbg !992, !tbaa !432
  %102 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %101, i32 0, i32 0, !dbg !993
  %103 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %102, i32 0, i32 0, !dbg !994
  store void (%struct.ipc_context*, %struct.uevent*)* @handle_port, void (%struct.ipc_context*, %struct.uevent*)** %103, align 4, !dbg !995, !tbaa !996
  %104 = load %struct.ipc_port_context*, %struct.ipc_port_context** %7, align 4, !dbg !997, !tbaa !432
  %105 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %104, i32 0, i32 2, !dbg !998
  call arm_aapcscc void @list_initialize(%struct.list_node* %105), !dbg !999
  store i32 0, i32* %6, align 4, !dbg !1000
  store i32 1, i32* %13, align 4
  br label %111, !dbg !1000

106:                                              ; preds = %76
  call void @llvm.dbg.label(metadata !914), !dbg !1001
  br label %107, !dbg !1000

107:                                              ; preds = %106, %95
  call void @llvm.dbg.label(metadata !915), !dbg !1002
  %108 = load i32, i32* %14, align 4, !dbg !1003, !tbaa !359
  %109 = call arm_aapcscc i32 @close(i32 %108), !dbg !1004
  %110 = load i32, i32* %12, align 4, !dbg !1005, !tbaa !359
  store i32 %110, i32* %6, align 4, !dbg !1006
  store i32 1, i32* %13, align 4
  br label %111, !dbg !1006

111:                                              ; preds = %107, %96
  %112 = bitcast i32* %14 to i8*, !dbg !1007
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %112) #6, !dbg !1007
  br label %113

113:                                              ; preds = %111, %52
  %114 = bitcast i32* %12 to i8*, !dbg !1007
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %114) #6, !dbg !1007
  %115 = load i32, i32* %6, align 4, !dbg !1007
  ret i32 %115, !dbg !1007
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @is_valid_port_ops(%struct.ipc_port_ops* %0) #0 !dbg !1008 {
  %2 = alloca %struct.ipc_port_ops*, align 4
  store %struct.ipc_port_ops* %0, %struct.ipc_port_ops** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_port_ops** %2, metadata !1013, metadata !DIExpression()), !dbg !1014
  %3 = load %struct.ipc_port_ops*, %struct.ipc_port_ops** %2, align 4, !dbg !1015, !tbaa !432
  %4 = getelementptr inbounds %struct.ipc_port_ops, %struct.ipc_port_ops* %3, i32 0, i32 0, !dbg !1016
  %5 = load %struct.ipc_channel_context* (%struct.ipc_port_context*, %struct.uuid*, i32)*, %struct.ipc_channel_context* (%struct.ipc_port_context*, %struct.uuid*, i32)** %4, align 4, !dbg !1016, !tbaa !1017
  %6 = icmp ne %struct.ipc_channel_context* (%struct.ipc_port_context*, %struct.uuid*, i32)* %5, null, !dbg !1018
  %7 = zext i1 %6 to i32, !dbg !1018
  ret i32 %7, !dbg !1019
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @maybe_grow_msg_buf(i32 %0) #0 !dbg !1020 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  %4 = alloca i8*, align 4
  %5 = alloca i32, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !1024, metadata !DIExpression()), !dbg !1029
  %6 = load i32, i32* %3, align 4, !dbg !1030, !tbaa !359
  %7 = load i32, i32* @msg_buf_size, align 4, !dbg !1031, !tbaa !359
  %8 = icmp ugt i32 %6, %7, !dbg !1032
  br i1 %8, label %9, label %24, !dbg !1033

9:                                                ; preds = %1
  %10 = bitcast i8** %4 to i8*, !dbg !1034
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %10) #6, !dbg !1034
  call void @llvm.dbg.declare(metadata i8** %4, metadata !1025, metadata !DIExpression()), !dbg !1035
  %11 = load i8*, i8** @msg_buf, align 4, !dbg !1036, !tbaa !432
  %12 = load i32, i32* %3, align 4, !dbg !1037, !tbaa !359
  %13 = call arm_aapcscc i8* @realloc(i8* %11, i32 %12), !dbg !1038
  store i8* %13, i8** %4, align 4, !dbg !1035, !tbaa !432
  %14 = load i8*, i8** %4, align 4, !dbg !1039, !tbaa !432
  %15 = icmp eq i8* %14, null, !dbg !1041
  br i1 %15, label %16, label %17, !dbg !1042

16:                                               ; preds = %9
  store i32 -5, i32* %2, align 4, !dbg !1043
  store i32 1, i32* %5, align 4
  br label %20, !dbg !1043

17:                                               ; preds = %9
  %18 = load i8*, i8** %4, align 4, !dbg !1045, !tbaa !432
  store i8* %18, i8** @msg_buf, align 4, !dbg !1046, !tbaa !432
  %19 = load i32, i32* %3, align 4, !dbg !1047, !tbaa !359
  store i32 %19, i32* @msg_buf_size, align 4, !dbg !1048, !tbaa !359
  store i32 0, i32* %5, align 4, !dbg !1049
  br label %20, !dbg !1049

20:                                               ; preds = %17, %16
  %21 = bitcast i8** %4 to i8*, !dbg !1049
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %21) #6, !dbg !1049
  %22 = load i32, i32* %5, align 4
  switch i32 %22, label %27 [
    i32 0, label %23
    i32 1, label %25
  ]

23:                                               ; preds = %20
  br label %24, !dbg !1050

24:                                               ; preds = %23, %1
  store i32 0, i32* %2, align 4, !dbg !1051
  br label %25, !dbg !1051

25:                                               ; preds = %24, %20
  %26 = load i32, i32* %2, align 4, !dbg !1052
  ret i32 %26, !dbg !1052

27:                                               ; preds = %20
  unreachable
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc void @handle_port(%struct.ipc_context* %0, %struct.uevent* %1) #0 !dbg !1053 {
  %3 = alloca %struct.ipc_context*, align 4
  %4 = alloca %struct.uevent*, align 4
  %5 = alloca %struct.ipc_port_context*, align 4
  store %struct.ipc_context* %0, %struct.ipc_context** %3, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_context** %3, metadata !1055, metadata !DIExpression()), !dbg !1058
  store %struct.uevent* %1, %struct.uevent** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %4, metadata !1056, metadata !DIExpression()), !dbg !1059
  %6 = bitcast %struct.ipc_port_context** %5 to i8*, !dbg !1060
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %6) #6, !dbg !1060
  call void @llvm.dbg.declare(metadata %struct.ipc_port_context** %5, metadata !1057, metadata !DIExpression()), !dbg !1061
  %7 = load %struct.ipc_context*, %struct.ipc_context** %3, align 4, !dbg !1062, !tbaa !432
  %8 = call arm_aapcscc %struct.ipc_port_context* @to_port_context(%struct.ipc_context* %7), !dbg !1063
  store %struct.ipc_port_context* %8, %struct.ipc_port_context** %5, align 4, !dbg !1061, !tbaa !432
  %9 = load %struct.ipc_port_context*, %struct.ipc_port_context** %5, align 4, !dbg !1064, !tbaa !432
  %10 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %9, i32 0, i32 1, !dbg !1064
  %11 = call arm_aapcscc i32 @is_valid_port_ops(%struct.ipc_port_ops* %10), !dbg !1064
  %12 = icmp ne i32 %11, 0, !dbg !1064
  br i1 %12, label %15, label %13, !dbg !1064

13:                                               ; preds = %2
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.26, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 192, i8* getelementptr inbounds ([12 x i8], [12 x i8]* @__func__.handle_port, i32 0, i32 0)) #7, !dbg !1064
  unreachable, !dbg !1064

14:                                               ; No predecessors!
  br label %15, !dbg !1064

15:                                               ; preds = %14, %2
  %16 = phi i1 [ true, %2 ], [ false, %14 ]
  %17 = zext i1 %16 to i32, !dbg !1064
  %18 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1065, !tbaa !432
  call arm_aapcscc void @handle_port_errors(%struct.uevent* %18), !dbg !1066
  %19 = load %struct.ipc_port_context*, %struct.ipc_port_context** %5, align 4, !dbg !1067, !tbaa !432
  %20 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1068, !tbaa !432
  %21 = call arm_aapcscc i32 @do_connect(%struct.ipc_port_context* %19, %struct.uevent* %20), !dbg !1069
  %22 = bitcast %struct.ipc_port_context** %5 to i8*, !dbg !1070
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %22) #6, !dbg !1070
  ret void, !dbg !1070
}

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc void @list_initialize(%struct.list_node* %0) #4 !dbg !1071 {
  %2 = alloca %struct.list_node*, align 4
  store %struct.list_node* %0, %struct.list_node** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.list_node** %2, metadata !1075, metadata !DIExpression()), !dbg !1076
  %3 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1077, !tbaa !432
  %4 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1078, !tbaa !432
  %5 = getelementptr inbounds %struct.list_node, %struct.list_node* %4, i32 0, i32 1, !dbg !1079
  store %struct.list_node* %3, %struct.list_node** %5, align 4, !dbg !1080, !tbaa !1081
  %6 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1082, !tbaa !432
  %7 = getelementptr inbounds %struct.list_node, %struct.list_node* %6, i32 0, i32 0, !dbg !1083
  store %struct.list_node* %3, %struct.list_node** %7, align 4, !dbg !1084, !tbaa !1085
  ret void, !dbg !1086
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.label(metadata) #2

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc %struct.ipc_port_context* @to_port_context(%struct.ipc_context* %0) #0 !dbg !1087 {
  %2 = alloca %struct.ipc_context*, align 4
  store %struct.ipc_context* %0, %struct.ipc_context** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_context** %2, metadata !1091, metadata !DIExpression()), !dbg !1092
  %3 = load %struct.ipc_context*, %struct.ipc_context** %2, align 4, !dbg !1093, !tbaa !432
  %4 = icmp ne %struct.ipc_context* %3, null, !dbg !1093
  br i1 %4, label %7, label %5, !dbg !1093

5:                                                ; preds = %1
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 77, i8* getelementptr inbounds ([16 x i8], [16 x i8]* @__func__.to_port_context, i32 0, i32 0)) #7, !dbg !1093
  unreachable, !dbg !1093

6:                                                ; No predecessors!
  br label %7, !dbg !1093

7:                                                ; preds = %6, %1
  %8 = phi i1 [ true, %1 ], [ false, %6 ]
  %9 = zext i1 %8 to i32, !dbg !1093
  %10 = load %struct.ipc_context*, %struct.ipc_context** %2, align 4, !dbg !1094, !tbaa !432
  %11 = ptrtoint %struct.ipc_context* %10 to i32, !dbg !1094
  %12 = sub i32 %11, 0, !dbg !1094
  %13 = inttoptr i32 %12 to %struct.ipc_port_context*, !dbg !1094
  ret %struct.ipc_port_context* %13, !dbg !1095
}

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc void @handle_port_errors(%struct.uevent* %0) #4 !dbg !1096 {
  %2 = alloca %struct.uevent*, align 4
  store %struct.uevent* %0, %struct.uevent** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %2, metadata !1098, metadata !DIExpression()), !dbg !1099
  %3 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1100, !tbaa !432
  %4 = getelementptr inbounds %struct.uevent, %struct.uevent* %3, i32 0, i32 1, !dbg !1102
  %5 = load i32, i32* %4, align 4, !dbg !1102, !tbaa !379
  %6 = and i32 %5, 2, !dbg !1103
  %7 = icmp ne i32 %6, 0, !dbg !1103
  br i1 %7, label %26, label %8, !dbg !1104

8:                                                ; preds = %1
  %9 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1105, !tbaa !432
  %10 = getelementptr inbounds %struct.uevent, %struct.uevent* %9, i32 0, i32 1, !dbg !1106
  %11 = load i32, i32* %10, align 4, !dbg !1106, !tbaa !379
  %12 = and i32 %11, 4, !dbg !1107
  %13 = icmp ne i32 %12, 0, !dbg !1107
  br i1 %13, label %26, label %14, !dbg !1108

14:                                               ; preds = %8
  %15 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1109, !tbaa !432
  %16 = getelementptr inbounds %struct.uevent, %struct.uevent* %15, i32 0, i32 1, !dbg !1110
  %17 = load i32, i32* %16, align 4, !dbg !1110, !tbaa !379
  %18 = and i32 %17, 8, !dbg !1111
  %19 = icmp ne i32 %18, 0, !dbg !1111
  br i1 %19, label %26, label %20, !dbg !1112

20:                                               ; preds = %14
  %21 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1113, !tbaa !432
  %22 = getelementptr inbounds %struct.uevent, %struct.uevent* %21, i32 0, i32 1, !dbg !1114
  %23 = load i32, i32* %22, align 4, !dbg !1114, !tbaa !379
  %24 = and i32 %23, 16, !dbg !1115
  %25 = icmp ne i32 %24, 0, !dbg !1115
  br i1 %25, label %26, label %46, !dbg !1116

26:                                               ; preds = %20, %14, %8, %1
  br label %27, !dbg !1117

27:                                               ; preds = %26
  br label %28, !dbg !1119

28:                                               ; preds = %27
  %29 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1123, !tbaa !432
  %30 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1123, !tbaa !432
  %31 = getelementptr inbounds %struct.uevent, %struct.uevent* %30, i32 0, i32 1, !dbg !1123
  %32 = load i32, i32* %31, align 4, !dbg !1123, !tbaa !379
  %33 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1123, !tbaa !432
  %34 = getelementptr inbounds %struct.uevent, %struct.uevent* %33, i32 0, i32 0, !dbg !1123
  %35 = load i32, i32* %34, align 4, !dbg !1123, !tbaa !374
  %36 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %29, i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.27, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 55, i32 %32, i32 %35), !dbg !1123
  %37 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1123, !tbaa !432
  %38 = getelementptr inbounds %struct.uevent, %struct.uevent* %37, i32 0, i32 1, !dbg !1123
  %39 = load i32, i32* %38, align 4, !dbg !1123, !tbaa !379
  %40 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1123, !tbaa !432
  %41 = getelementptr inbounds %struct.uevent, %struct.uevent* %40, i32 0, i32 0, !dbg !1123
  %42 = load i32, i32* %41, align 4, !dbg !1123, !tbaa !374
  %43 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.27, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 55, i32 %39, i32 %42), !dbg !1123
  br label %44, !dbg !1123

44:                                               ; preds = %28
  br label %45, !dbg !1125

45:                                               ; preds = %44
  call arm_aapcscc void @abort() #7, !dbg !1126
  unreachable, !dbg !1126

46:                                               ; preds = %20
  ret void, !dbg !1127
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @do_connect(%struct.ipc_port_context* %0, %struct.uevent* %1) #0 !dbg !1128 {
  %3 = alloca i32, align 4
  %4 = alloca %struct.ipc_port_context*, align 4
  %5 = alloca %struct.uevent*, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.ipc_channel_context*, align 4
  %9 = alloca %struct.uuid, align 4
  %10 = alloca i32, align 4
  store %struct.ipc_port_context* %0, %struct.ipc_port_context** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_port_context** %4, metadata !1132, metadata !DIExpression()), !dbg !1142
  store %struct.uevent* %1, %struct.uevent** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %5, metadata !1133, metadata !DIExpression()), !dbg !1143
  %11 = bitcast i32* %6 to i8*, !dbg !1144
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %11) #6, !dbg !1144
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1134, metadata !DIExpression()), !dbg !1145
  %12 = bitcast i32* %7 to i8*, !dbg !1146
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %12) #6, !dbg !1146
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1135, metadata !DIExpression()), !dbg !1147
  %13 = bitcast %struct.ipc_channel_context** %8 to i8*, !dbg !1148
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %13) #6, !dbg !1148
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %8, metadata !1136, metadata !DIExpression()), !dbg !1149
  %14 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1150, !tbaa !432
  %15 = getelementptr inbounds %struct.uevent, %struct.uevent* %14, i32 0, i32 1, !dbg !1151
  %16 = load i32, i32* %15, align 4, !dbg !1151, !tbaa !379
  %17 = and i32 %16, 1, !dbg !1152
  %18 = icmp ne i32 %17, 0, !dbg !1152
  br i1 %18, label %19, label %114, !dbg !1153

19:                                               ; preds = %2
  %20 = bitcast %struct.uuid* %9 to i8*, !dbg !1154
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %20) #6, !dbg !1154
  call void @llvm.dbg.declare(metadata %struct.uuid* %9, metadata !1137, metadata !DIExpression()), !dbg !1155
  %21 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1156, !tbaa !432
  %22 = getelementptr inbounds %struct.uevent, %struct.uevent* %21, i32 0, i32 0, !dbg !1157
  %23 = load i32, i32* %22, align 4, !dbg !1157, !tbaa !374
  %24 = call arm_aapcscc i32 @accept(i32 %23, %struct.uuid* %9), !dbg !1158
  store i32 %24, i32* %6, align 4, !dbg !1159, !tbaa !359
  %25 = load i32, i32* %6, align 4, !dbg !1160, !tbaa !359
  %26 = icmp slt i32 %25, 0, !dbg !1162
  br i1 %26, label %27, label %46, !dbg !1163

27:                                               ; preds = %19
  br label %28, !dbg !1164

28:                                               ; preds = %27
  br label %29, !dbg !1166

29:                                               ; preds = %28
  %30 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1170, !tbaa !432
  %31 = load i32, i32* %6, align 4, !dbg !1170, !tbaa !359
  %32 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1170, !tbaa !432
  %33 = getelementptr inbounds %struct.uevent, %struct.uevent* %32, i32 0, i32 0, !dbg !1170
  %34 = load i32, i32* %33, align 4, !dbg !1170, !tbaa !374
  %35 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %30, i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.28, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 97, i32 %31, i32 %34), !dbg !1170
  %36 = load i32, i32* %6, align 4, !dbg !1170, !tbaa !359
  %37 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1170, !tbaa !432
  %38 = getelementptr inbounds %struct.uevent, %struct.uevent* %37, i32 0, i32 0, !dbg !1170
  %39 = load i32, i32* %38, align 4, !dbg !1170, !tbaa !374
  %40 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.28, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 97, i32 %36, i32 %39), !dbg !1170
  br label %41, !dbg !1170

41:                                               ; preds = %29
  br label %42, !dbg !1170

42:                                               ; preds = %41
  br label %43, !dbg !1172

43:                                               ; preds = %42
  br label %44, !dbg !1172

44:                                               ; preds = %43
  %45 = load i32, i32* %6, align 4, !dbg !1173, !tbaa !359
  store i32 %45, i32* %3, align 4, !dbg !1174
  store i32 1, i32* %10, align 4
  br label %110, !dbg !1174

46:                                               ; preds = %19
  %47 = load i32, i32* %6, align 4, !dbg !1175, !tbaa !359
  store i32 %47, i32* %7, align 4, !dbg !1176, !tbaa !359
  %48 = load %struct.ipc_port_context*, %struct.ipc_port_context** %4, align 4, !dbg !1177, !tbaa !432
  %49 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %48, i32 0, i32 1, !dbg !1178
  %50 = getelementptr inbounds %struct.ipc_port_ops, %struct.ipc_port_ops* %49, i32 0, i32 0, !dbg !1179
  %51 = load %struct.ipc_channel_context* (%struct.ipc_port_context*, %struct.uuid*, i32)*, %struct.ipc_channel_context* (%struct.ipc_port_context*, %struct.uuid*, i32)** %50, align 4, !dbg !1179, !tbaa !1180
  %52 = load %struct.ipc_port_context*, %struct.ipc_port_context** %4, align 4, !dbg !1181, !tbaa !432
  %53 = load i32, i32* %7, align 4, !dbg !1182, !tbaa !359
  %54 = call arm_aapcscc %struct.ipc_channel_context* %51(%struct.ipc_port_context* %52, %struct.uuid* %9, i32 %53), !dbg !1177
  store %struct.ipc_channel_context* %54, %struct.ipc_channel_context** %8, align 4, !dbg !1183, !tbaa !432
  %55 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1184, !tbaa !432
  %56 = icmp eq %struct.ipc_channel_context* %55, null, !dbg !1186
  br i1 %56, label %57, label %69, !dbg !1187

57:                                               ; preds = %46
  br label %58, !dbg !1188

58:                                               ; preds = %57
  br label %59, !dbg !1190

59:                                               ; preds = %58
  %60 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1194, !tbaa !432
  %61 = load i32, i32* %6, align 4, !dbg !1194, !tbaa !359
  %62 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %60, i8* getelementptr inbounds ([53 x i8], [53 x i8]* @.str.29, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 106, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__func__.do_connect, i32 0, i32 0), i32 %61), !dbg !1194
  %63 = load i32, i32* %6, align 4, !dbg !1194, !tbaa !359
  %64 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([53 x i8], [53 x i8]* @.str.29, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 106, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__func__.do_connect, i32 0, i32 0), i32 %63), !dbg !1194
  br label %65, !dbg !1194

65:                                               ; preds = %59
  br label %66, !dbg !1194

66:                                               ; preds = %65
  br label %67, !dbg !1196

67:                                               ; preds = %66
  br label %68, !dbg !1196

68:                                               ; preds = %67
  store i32 -1, i32* %6, align 4, !dbg !1197, !tbaa !359
  store i32 10, i32* %10, align 4
  br label %110, !dbg !1198

69:                                               ; preds = %46
  %70 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1199, !tbaa !432
  %71 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %70, i32 0, i32 1, !dbg !1199
  %72 = call arm_aapcscc zeroext i1 @is_valid_chan_ops(%struct.ipc_channel_ops* %71), !dbg !1199
  br i1 %72, label %75, label %73, !dbg !1199

73:                                               ; preds = %69
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([34 x i8], [34 x i8]* @.str.30, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 111, i8* getelementptr inbounds ([11 x i8], [11 x i8]* @__func__.do_connect, i32 0, i32 0)) #7, !dbg !1199
  unreachable, !dbg !1199

74:                                               ; No predecessors!
  br label %75, !dbg !1199

75:                                               ; preds = %74, %69
  %76 = phi i1 [ true, %69 ], [ false, %74 ]
  %77 = zext i1 %76 to i32, !dbg !1199
  %78 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1200, !tbaa !432
  %79 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %78, i32 0, i32 0, !dbg !1201
  %80 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %79, i32 0, i32 0, !dbg !1202
  store void (%struct.ipc_context*, %struct.uevent*)* @handle_channel, void (%struct.ipc_context*, %struct.uevent*)** %80, align 4, !dbg !1203, !tbaa !1204
  %81 = load i32, i32* %7, align 4, !dbg !1205, !tbaa !359
  %82 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1206, !tbaa !432
  %83 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %82, i32 0, i32 0, !dbg !1207
  %84 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %83, i32 0, i32 1, !dbg !1208
  store i32 %81, i32* %84, align 4, !dbg !1209, !tbaa !499
  %85 = load i32, i32* %7, align 4, !dbg !1210, !tbaa !359
  %86 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1211, !tbaa !432
  %87 = bitcast %struct.ipc_channel_context* %86 to i8*, !dbg !1211
  %88 = call arm_aapcscc i32 @set_cookie(i32 %85, i8* %87), !dbg !1212
  store i32 %88, i32* %6, align 4, !dbg !1213, !tbaa !359
  %89 = load i32, i32* %6, align 4, !dbg !1214, !tbaa !359
  %90 = icmp slt i32 %89, 0, !dbg !1216
  br i1 %90, label %91, label %105, !dbg !1217

91:                                               ; preds = %75
  br label %92, !dbg !1218

92:                                               ; preds = %91
  br label %93, !dbg !1220

93:                                               ; preds = %92
  %94 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1224, !tbaa !432
  %95 = load i32, i32* %6, align 4, !dbg !1224, !tbaa !359
  %96 = load i32, i32* %7, align 4, !dbg !1224, !tbaa !359
  %97 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %94, i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.31, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 118, i32 %95, i32 %96), !dbg !1224
  %98 = load i32, i32* %6, align 4, !dbg !1224, !tbaa !359
  %99 = load i32, i32* %7, align 4, !dbg !1224, !tbaa !359
  %100 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([46 x i8], [46 x i8]* @.str.31, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 118, i32 %98, i32 %99), !dbg !1224
  br label %101, !dbg !1224

101:                                              ; preds = %93
  br label %102, !dbg !1224

102:                                              ; preds = %101
  br label %103, !dbg !1226

103:                                              ; preds = %102
  br label %104, !dbg !1226

104:                                              ; preds = %103
  store i32 15, i32* %10, align 4
  br label %110, !dbg !1227

105:                                              ; preds = %75
  %106 = load %struct.ipc_port_context*, %struct.ipc_port_context** %4, align 4, !dbg !1228, !tbaa !432
  %107 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %106, i32 0, i32 2, !dbg !1229
  %108 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1230, !tbaa !432
  %109 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %108, i32 0, i32 2, !dbg !1231
  call arm_aapcscc void @list_add_tail(%struct.list_node* %107, %struct.list_node* %109), !dbg !1232
  store i32 0, i32* %10, align 4, !dbg !1233
  br label %110, !dbg !1233

110:                                              ; preds = %105, %104, %68, %44
  %111 = bitcast %struct.uuid* %9 to i8*, !dbg !1233
  call void @llvm.lifetime.end.p0i8(i64 16, i8* %111) #6, !dbg !1233
  %112 = load i32, i32* %10, align 4
  switch i32 %112, label %125 [
    i32 0, label %113
    i32 15, label %115
    i32 10, label %121
  ]

113:                                              ; preds = %110
  br label %114, !dbg !1234

114:                                              ; preds = %113, %2
  store i32 0, i32* %3, align 4, !dbg !1235
  store i32 1, i32* %10, align 4
  br label %125, !dbg !1235

115:                                              ; preds = %110
  call void @llvm.dbg.label(metadata !1140), !dbg !1236
  %116 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1237, !tbaa !432
  %117 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %116, i32 0, i32 1, !dbg !1238
  %118 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %117, i32 0, i32 1, !dbg !1239
  %119 = load void (%struct.ipc_channel_context*)*, void (%struct.ipc_channel_context*)** %118, align 4, !dbg !1239, !tbaa !443
  %120 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %8, align 4, !dbg !1240, !tbaa !432
  call arm_aapcscc void %119(%struct.ipc_channel_context* %120), !dbg !1237
  br label %121, !dbg !1237

121:                                              ; preds = %115, %110
  call void @llvm.dbg.label(metadata !1141), !dbg !1241
  %122 = load i32, i32* %7, align 4, !dbg !1242, !tbaa !359
  %123 = call arm_aapcscc i32 @close(i32 %122), !dbg !1243
  %124 = load i32, i32* %6, align 4, !dbg !1244, !tbaa !359
  store i32 %124, i32* %3, align 4, !dbg !1245
  store i32 1, i32* %10, align 4
  br label %125, !dbg !1245

125:                                              ; preds = %121, %114, %110
  %126 = bitcast %struct.ipc_channel_context** %8 to i8*, !dbg !1246
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %126) #6, !dbg !1246
  %127 = bitcast i32* %7 to i8*, !dbg !1246
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %127) #6, !dbg !1246
  %128 = bitcast i32* %6 to i8*, !dbg !1246
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %128) #6, !dbg !1246
  %129 = load i32, i32* %3, align 4, !dbg !1246
  ret i32 %129, !dbg !1246
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc zeroext i1 @is_valid_chan_ops(%struct.ipc_channel_ops* %0) #0 !dbg !1247 {
  %2 = alloca %struct.ipc_channel_ops*, align 4
  store %struct.ipc_channel_ops* %0, %struct.ipc_channel_ops** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_ops** %2, metadata !1252, metadata !DIExpression()), !dbg !1253
  %3 = load %struct.ipc_channel_ops*, %struct.ipc_channel_ops** %2, align 4, !dbg !1254, !tbaa !432
  %4 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %3, i32 0, i32 1, !dbg !1255
  %5 = load void (%struct.ipc_channel_context*)*, void (%struct.ipc_channel_context*)** %4, align 4, !dbg !1255, !tbaa !1256
  %6 = icmp ne void (%struct.ipc_channel_context*)* %5, null, !dbg !1257
  ret i1 %6, !dbg !1258
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc void @handle_channel(%struct.ipc_context* %0, %struct.uevent* %1) #0 !dbg !1259 {
  %3 = alloca %struct.ipc_context*, align 4
  %4 = alloca %struct.uevent*, align 4
  %5 = alloca %struct.ipc_channel_context*, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store %struct.ipc_context* %0, %struct.ipc_context** %3, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_context** %3, metadata !1261, metadata !DIExpression()), !dbg !1269
  store %struct.uevent* %1, %struct.uevent** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %4, metadata !1262, metadata !DIExpression()), !dbg !1270
  %8 = bitcast %struct.ipc_channel_context** %5 to i8*, !dbg !1271
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %8) #6, !dbg !1271
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %5, metadata !1263, metadata !DIExpression()), !dbg !1272
  %9 = load %struct.ipc_context*, %struct.ipc_context** %3, align 4, !dbg !1273, !tbaa !432
  %10 = call arm_aapcscc %struct.ipc_channel_context* @to_channel_context(%struct.ipc_context* %9), !dbg !1274
  store %struct.ipc_channel_context* %10, %struct.ipc_channel_context** %5, align 4, !dbg !1272, !tbaa !432
  %11 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !1275, !tbaa !432
  %12 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %11, i32 0, i32 1, !dbg !1275
  %13 = call arm_aapcscc zeroext i1 @is_valid_chan_ops(%struct.ipc_channel_ops* %12), !dbg !1275
  br i1 %13, label %16, label %14, !dbg !1275

14:                                               ; preds = %2
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.32, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 201, i8* getelementptr inbounds ([15 x i8], [15 x i8]* @__func__.handle_channel, i32 0, i32 0)) #7, !dbg !1275
  unreachable, !dbg !1275

15:                                               ; No predecessors!
  br label %16, !dbg !1275

16:                                               ; preds = %15, %2
  %17 = phi i1 [ true, %2 ], [ false, %15 ]
  %18 = zext i1 %17 to i32, !dbg !1275
  %19 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1276, !tbaa !432
  call arm_aapcscc void @handle_chan_errors(%struct.uevent* %19), !dbg !1277
  %20 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1278, !tbaa !432
  %21 = getelementptr inbounds %struct.uevent, %struct.uevent* %20, i32 0, i32 1, !dbg !1279
  %22 = load i32, i32* %21, align 4, !dbg !1279, !tbaa !379
  %23 = and i32 %22, 8, !dbg !1280
  %24 = icmp ne i32 %23, 0, !dbg !1280
  br i1 %24, label %25, label %76, !dbg !1281

25:                                               ; preds = %16
  %26 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !1282, !tbaa !432
  %27 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %26, i32 0, i32 1, !dbg !1283
  %28 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %27, i32 0, i32 0, !dbg !1284
  %29 = load i32 (%struct.ipc_channel_context*, i8*, i32)*, i32 (%struct.ipc_channel_context*, i8*, i32)** %28, align 4, !dbg !1284, !tbaa !452
  %30 = icmp ne i32 (%struct.ipc_channel_context*, i8*, i32)* %29, null, !dbg !1285
  br i1 %30, label %31, label %57, !dbg !1286

31:                                               ; preds = %25
  %32 = bitcast i32* %6 to i8*, !dbg !1287
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %32) #6, !dbg !1287
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1264, metadata !DIExpression()), !dbg !1288
  %33 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !1289, !tbaa !432
  %34 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1290, !tbaa !432
  %35 = call arm_aapcscc i32 @do_handle_msg(%struct.ipc_channel_context* %33, %struct.uevent* %34), !dbg !1291
  store i32 %35, i32* %6, align 4, !dbg !1288, !tbaa !359
  %36 = load i32, i32* %6, align 4, !dbg !1292, !tbaa !359
  %37 = icmp slt i32 %36, 0, !dbg !1294
  br i1 %37, label %38, label %52, !dbg !1295

38:                                               ; preds = %31
  br label %39, !dbg !1296

39:                                               ; preds = %38
  br label %40, !dbg !1298

40:                                               ; preds = %39
  %41 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1302, !tbaa !432
  %42 = load i32, i32* %6, align 4, !dbg !1302, !tbaa !359
  %43 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %41, i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.33, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 211, i32 %42), !dbg !1302
  %44 = load i32, i32* %6, align 4, !dbg !1302, !tbaa !359
  %45 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([51 x i8], [51 x i8]* @.str.33, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 211, i32 %44), !dbg !1302
  br label %46, !dbg !1302

46:                                               ; preds = %40
  br label %47, !dbg !1302

47:                                               ; preds = %46
  br label %48, !dbg !1304

48:                                               ; preds = %47
  br label %49, !dbg !1304

49:                                               ; preds = %48
  %50 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !1305, !tbaa !432
  %51 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1306, !tbaa !432
  call arm_aapcscc void @do_disconnect(%struct.ipc_channel_context* %50, %struct.uevent* %51), !dbg !1307
  store i32 1, i32* %7, align 4
  br label %53, !dbg !1308

52:                                               ; preds = %31
  store i32 0, i32* %7, align 4, !dbg !1309
  br label %53, !dbg !1309

53:                                               ; preds = %52, %49
  %54 = bitcast i32* %6 to i8*, !dbg !1309
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %54) #6, !dbg !1309
  %55 = load i32, i32* %7, align 4
  switch i32 %55, label %86 [
    i32 0, label %56
  ]

56:                                               ; preds = %53
  br label %75, !dbg !1310

57:                                               ; preds = %25
  br label %58, !dbg !1311

58:                                               ; preds = %57
  br label %59, !dbg !1313

59:                                               ; preds = %58
  %60 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1317, !tbaa !432
  %61 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1317, !tbaa !432
  %62 = getelementptr inbounds %struct.uevent, %struct.uevent* %61, i32 0, i32 0, !dbg !1317
  %63 = load i32, i32* %62, align 4, !dbg !1317, !tbaa !374
  %64 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %60, i8* getelementptr inbounds ([63 x i8], [63 x i8]* @.str.34, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 217, i32 %63), !dbg !1317
  %65 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1317, !tbaa !432
  %66 = getelementptr inbounds %struct.uevent, %struct.uevent* %65, i32 0, i32 0, !dbg !1317
  %67 = load i32, i32* %66, align 4, !dbg !1317, !tbaa !374
  %68 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([63 x i8], [63 x i8]* @.str.34, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 217, i32 %67), !dbg !1317
  br label %69, !dbg !1317

69:                                               ; preds = %59
  br label %70, !dbg !1317

70:                                               ; preds = %69
  br label %71, !dbg !1319

71:                                               ; preds = %70
  br label %72, !dbg !1319

72:                                               ; preds = %71
  %73 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !1320, !tbaa !432
  %74 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1321, !tbaa !432
  call arm_aapcscc void @do_disconnect(%struct.ipc_channel_context* %73, %struct.uevent* %74), !dbg !1322
  store i32 1, i32* %7, align 4
  br label %86, !dbg !1323

75:                                               ; preds = %56
  br label %76, !dbg !1324

76:                                               ; preds = %75, %16
  %77 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1325, !tbaa !432
  %78 = getelementptr inbounds %struct.uevent, %struct.uevent* %77, i32 0, i32 1, !dbg !1327
  %79 = load i32, i32* %78, align 4, !dbg !1327, !tbaa !379
  %80 = and i32 %79, 4, !dbg !1328
  %81 = icmp ne i32 %80, 0, !dbg !1328
  br i1 %81, label %82, label %85, !dbg !1329

82:                                               ; preds = %76
  %83 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !1330, !tbaa !432
  %84 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1332, !tbaa !432
  call arm_aapcscc void @do_disconnect(%struct.ipc_channel_context* %83, %struct.uevent* %84), !dbg !1333
  br label %85, !dbg !1334

85:                                               ; preds = %82, %76
  store i32 0, i32* %7, align 4, !dbg !1335
  br label %86, !dbg !1335

86:                                               ; preds = %85, %72, %53
  %87 = bitcast %struct.ipc_channel_context** %5 to i8*, !dbg !1335
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %87) #6, !dbg !1335
  %88 = load i32, i32* %7, align 4
  switch i32 %88, label %90 [
    i32 0, label %89
    i32 1, label %89
  ]

89:                                               ; preds = %86, %86
  ret void, !dbg !1335

90:                                               ; preds = %86
  unreachable
}

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc void @list_add_tail(%struct.list_node* %0, %struct.list_node* %1) #4 !dbg !1336 {
  %3 = alloca %struct.list_node*, align 4
  %4 = alloca %struct.list_node*, align 4
  store %struct.list_node* %0, %struct.list_node** %3, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.list_node** %3, metadata !1340, metadata !DIExpression()), !dbg !1342
  store %struct.list_node* %1, %struct.list_node** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.list_node** %4, metadata !1341, metadata !DIExpression()), !dbg !1343
  %5 = load %struct.list_node*, %struct.list_node** %3, align 4, !dbg !1344, !tbaa !432
  %6 = getelementptr inbounds %struct.list_node, %struct.list_node* %5, i32 0, i32 0, !dbg !1345
  %7 = load %struct.list_node*, %struct.list_node** %6, align 4, !dbg !1345, !tbaa !1085
  %8 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1346, !tbaa !432
  %9 = getelementptr inbounds %struct.list_node, %struct.list_node* %8, i32 0, i32 0, !dbg !1347
  store %struct.list_node* %7, %struct.list_node** %9, align 4, !dbg !1348, !tbaa !1085
  %10 = load %struct.list_node*, %struct.list_node** %3, align 4, !dbg !1349, !tbaa !432
  %11 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1350, !tbaa !432
  %12 = getelementptr inbounds %struct.list_node, %struct.list_node* %11, i32 0, i32 1, !dbg !1351
  store %struct.list_node* %10, %struct.list_node** %12, align 4, !dbg !1352, !tbaa !1081
  %13 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1353, !tbaa !432
  %14 = load %struct.list_node*, %struct.list_node** %3, align 4, !dbg !1354, !tbaa !432
  %15 = getelementptr inbounds %struct.list_node, %struct.list_node* %14, i32 0, i32 0, !dbg !1355
  %16 = load %struct.list_node*, %struct.list_node** %15, align 4, !dbg !1355, !tbaa !1085
  %17 = getelementptr inbounds %struct.list_node, %struct.list_node* %16, i32 0, i32 1, !dbg !1356
  store %struct.list_node* %13, %struct.list_node** %17, align 4, !dbg !1357, !tbaa !1081
  %18 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1358, !tbaa !432
  %19 = load %struct.list_node*, %struct.list_node** %3, align 4, !dbg !1359, !tbaa !432
  %20 = getelementptr inbounds %struct.list_node, %struct.list_node* %19, i32 0, i32 0, !dbg !1360
  store %struct.list_node* %18, %struct.list_node** %20, align 4, !dbg !1361, !tbaa !1085
  ret void, !dbg !1362
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc %struct.ipc_channel_context* @to_channel_context(%struct.ipc_context* %0) #0 !dbg !1363 {
  %2 = alloca %struct.ipc_context*, align 4
  store %struct.ipc_context* %0, %struct.ipc_context** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_context** %2, metadata !1367, metadata !DIExpression()), !dbg !1368
  %3 = load %struct.ipc_context*, %struct.ipc_context** %2, align 4, !dbg !1369, !tbaa !432
  %4 = icmp ne %struct.ipc_context* %3, null, !dbg !1369
  br i1 %4, label %7, label %5, !dbg !1369

5:                                                ; preds = %1
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([8 x i8], [8 x i8]* @.str.10, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 83, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @__func__.to_channel_context, i32 0, i32 0)) #7, !dbg !1369
  unreachable, !dbg !1369

6:                                                ; No predecessors!
  br label %7, !dbg !1369

7:                                                ; preds = %6, %1
  %8 = phi i1 [ true, %1 ], [ false, %6 ]
  %9 = zext i1 %8 to i32, !dbg !1369
  %10 = load %struct.ipc_context*, %struct.ipc_context** %2, align 4, !dbg !1370, !tbaa !432
  %11 = ptrtoint %struct.ipc_context* %10 to i32, !dbg !1370
  %12 = sub i32 %11, 0, !dbg !1370
  %13 = inttoptr i32 %12 to %struct.ipc_channel_context*, !dbg !1370
  ret %struct.ipc_channel_context* %13, !dbg !1371
}

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc void @handle_chan_errors(%struct.uevent* %0) #4 !dbg !1372 {
  %2 = alloca %struct.uevent*, align 4
  store %struct.uevent* %0, %struct.uevent** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %2, metadata !1374, metadata !DIExpression()), !dbg !1375
  %3 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1376, !tbaa !432
  %4 = getelementptr inbounds %struct.uevent, %struct.uevent* %3, i32 0, i32 1, !dbg !1378
  %5 = load i32, i32* %4, align 4, !dbg !1378, !tbaa !379
  %6 = and i32 %5, 2, !dbg !1379
  %7 = icmp ne i32 %6, 0, !dbg !1379
  br i1 %7, label %14, label %8, !dbg !1380

8:                                                ; preds = %1
  %9 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1381, !tbaa !432
  %10 = getelementptr inbounds %struct.uevent, %struct.uevent* %9, i32 0, i32 1, !dbg !1382
  %11 = load i32, i32* %10, align 4, !dbg !1382, !tbaa !379
  %12 = and i32 %11, 1, !dbg !1383
  %13 = icmp ne i32 %12, 0, !dbg !1383
  br i1 %13, label %14, label %34, !dbg !1384

14:                                               ; preds = %8, %1
  br label %15, !dbg !1385

15:                                               ; preds = %14
  br label %16, !dbg !1387

16:                                               ; preds = %15
  %17 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1391, !tbaa !432
  %18 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1391, !tbaa !432
  %19 = getelementptr inbounds %struct.uevent, %struct.uevent* %18, i32 0, i32 1, !dbg !1391
  %20 = load i32, i32* %19, align 4, !dbg !1391, !tbaa !379
  %21 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1391, !tbaa !432
  %22 = getelementptr inbounds %struct.uevent, %struct.uevent* %21, i32 0, i32 0, !dbg !1391
  %23 = load i32, i32* %22, align 4, !dbg !1391, !tbaa !374
  %24 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %17, i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.35, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 63, i32 %20, i32 %23), !dbg !1391
  %25 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1391, !tbaa !432
  %26 = getelementptr inbounds %struct.uevent, %struct.uevent* %25, i32 0, i32 1, !dbg !1391
  %27 = load i32, i32* %26, align 4, !dbg !1391, !tbaa !379
  %28 = load %struct.uevent*, %struct.uevent** %2, align 4, !dbg !1391, !tbaa !432
  %29 = getelementptr inbounds %struct.uevent, %struct.uevent* %28, i32 0, i32 0, !dbg !1391
  %30 = load i32, i32* %29, align 4, !dbg !1391, !tbaa !374
  %31 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.35, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 63, i32 %27, i32 %30), !dbg !1391
  br label %32, !dbg !1391

32:                                               ; preds = %16
  br label %33, !dbg !1393

33:                                               ; preds = %32
  call arm_aapcscc void @abort() #7, !dbg !1394
  unreachable, !dbg !1394

34:                                               ; preds = %8
  ret void, !dbg !1395
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc i32 @do_handle_msg(%struct.ipc_channel_context* %0, %struct.uevent* %1) #0 !dbg !1396 {
  %3 = alloca i32, align 4
  %4 = alloca %struct.ipc_channel_context*, align 4
  %5 = alloca %struct.uevent*, align 4
  %6 = alloca i32, align 4
  %7 = alloca %struct.ipc_msg_info, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca %struct.iovec, align 4
  %11 = alloca %struct.ipc_msg, align 4
  store %struct.ipc_channel_context* %0, %struct.ipc_channel_context** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %4, metadata !1400, metadata !DIExpression()), !dbg !1411
  store %struct.uevent* %1, %struct.uevent** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %5, metadata !1401, metadata !DIExpression()), !dbg !1412
  %12 = bitcast i32* %6 to i8*, !dbg !1413
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %12) #6, !dbg !1413
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1402, metadata !DIExpression()), !dbg !1414
  %13 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1415, !tbaa !432
  %14 = getelementptr inbounds %struct.uevent, %struct.uevent* %13, i32 0, i32 0, !dbg !1416
  %15 = load i32, i32* %14, align 4, !dbg !1416, !tbaa !374
  store i32 %15, i32* %6, align 4, !dbg !1414, !tbaa !359
  %16 = bitcast %struct.ipc_msg_info* %7 to i8*, !dbg !1417
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %16) #6, !dbg !1417
  call void @llvm.dbg.declare(metadata %struct.ipc_msg_info* %7, metadata !1403, metadata !DIExpression()), !dbg !1418
  %17 = bitcast i32* %8 to i8*, !dbg !1419
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %17) #6, !dbg !1419
  call void @llvm.dbg.declare(metadata i32* %8, metadata !1405, metadata !DIExpression()), !dbg !1420
  %18 = load i32, i32* %6, align 4, !dbg !1421, !tbaa !359
  %19 = call arm_aapcscc i32 @get_msg(i32 %18, %struct.ipc_msg_info* %7), !dbg !1422
  store i32 %19, i32* %8, align 4, !dbg !1420, !tbaa !359
  %20 = load i32, i32* %8, align 4, !dbg !1423, !tbaa !359
  %21 = icmp eq i32 %20, -4, !dbg !1425
  br i1 %21, label %22, label %23, !dbg !1426

22:                                               ; preds = %2
  store i32 0, i32* %3, align 4, !dbg !1427
  store i32 1, i32* %9, align 4
  br label %135, !dbg !1427

23:                                               ; preds = %2
  %24 = load i32, i32* %8, align 4, !dbg !1428, !tbaa !359
  %25 = icmp ne i32 %24, 0, !dbg !1430
  br i1 %25, label %26, label %41, !dbg !1431

26:                                               ; preds = %23
  br label %27, !dbg !1432

27:                                               ; preds = %26
  br label %28, !dbg !1434

28:                                               ; preds = %27
  %29 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1438, !tbaa !432
  %30 = load i32, i32* %8, align 4, !dbg !1438, !tbaa !359
  %31 = load i32, i32* %6, align 4, !dbg !1438, !tbaa !359
  %32 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %29, i8* getelementptr inbounds ([66 x i8], [66 x i8]* @.str.36, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 144, i32 %30, i32 %31), !dbg !1438
  %33 = load i32, i32* %8, align 4, !dbg !1438, !tbaa !359
  %34 = load i32, i32* %6, align 4, !dbg !1438, !tbaa !359
  %35 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([66 x i8], [66 x i8]* @.str.36, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 144, i32 %33, i32 %34), !dbg !1438
  br label %36, !dbg !1438

36:                                               ; preds = %28
  br label %37, !dbg !1438

37:                                               ; preds = %36
  br label %38, !dbg !1440

38:                                               ; preds = %37
  br label %39, !dbg !1440

39:                                               ; preds = %38
  %40 = load i32, i32* %8, align 4, !dbg !1441, !tbaa !359
  store i32 %40, i32* %3, align 4, !dbg !1442
  store i32 1, i32* %9, align 4
  br label %135, !dbg !1442

41:                                               ; preds = %23
  %42 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 0, !dbg !1443
  %43 = load i32, i32* %42, align 4, !dbg !1443, !tbaa !605
  %44 = icmp ugt i32 %43, 4096, !dbg !1445
  br i1 %44, label %45, label %63, !dbg !1446

45:                                               ; preds = %41
  br label %46, !dbg !1447

46:                                               ; preds = %45
  br label %47, !dbg !1449

47:                                               ; preds = %46
  %48 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1453, !tbaa !432
  %49 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 0, !dbg !1453
  %50 = load i32, i32* %49, align 4, !dbg !1453, !tbaa !605
  %51 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %48, i8* getelementptr inbounds ([35 x i8], [35 x i8]* @.str.37, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 149, i8* getelementptr inbounds ([14 x i8], [14 x i8]* @__func__.do_handle_msg, i32 0, i32 0), i32 %50), !dbg !1453
  %52 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 0, !dbg !1453
  %53 = load i32, i32* %52, align 4, !dbg !1453, !tbaa !605
  %54 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([35 x i8], [35 x i8]* @.str.37, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 149, i8* getelementptr inbounds ([14 x i8], [14 x i8]* @__func__.do_handle_msg, i32 0, i32 0), i32 %53), !dbg !1453
  br label %55, !dbg !1453

55:                                               ; preds = %47
  br label %56, !dbg !1453

56:                                               ; preds = %55
  br label %57, !dbg !1455

57:                                               ; preds = %56
  br label %58, !dbg !1455

58:                                               ; preds = %57
  %59 = load i32, i32* %6, align 4, !dbg !1456, !tbaa !359
  %60 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 1, !dbg !1457
  %61 = load i32, i32* %60, align 4, !dbg !1457, !tbaa !621
  %62 = call arm_aapcscc i32 @put_msg(i32 %59, i32 %61), !dbg !1458
  store i32 -9, i32* %3, align 4, !dbg !1459
  store i32 1, i32* %9, align 4
  br label %135, !dbg !1459

63:                                               ; preds = %41
  %64 = bitcast %struct.iovec* %10 to i8*, !dbg !1460
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %64) #6, !dbg !1460
  call void @llvm.dbg.declare(metadata %struct.iovec* %10, metadata !1406, metadata !DIExpression()), !dbg !1461
  %65 = getelementptr inbounds %struct.iovec, %struct.iovec* %10, i32 0, i32 0, !dbg !1462
  %66 = load i8*, i8** @msg_buf, align 4, !dbg !1463, !tbaa !432
  store i8* %66, i8** %65, align 4, !dbg !1462, !tbaa !482
  %67 = getelementptr inbounds %struct.iovec, %struct.iovec* %10, i32 0, i32 1, !dbg !1462
  %68 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 0, !dbg !1464
  %69 = load i32, i32* %68, align 4, !dbg !1464, !tbaa !605
  store i32 %69, i32* %67, align 4, !dbg !1462, !tbaa !485
  %70 = bitcast %struct.ipc_msg* %11 to i8*, !dbg !1465
  call void @llvm.lifetime.start.p0i8(i64 16, i8* %70) #6, !dbg !1465
  call void @llvm.dbg.declare(metadata %struct.ipc_msg* %11, metadata !1407, metadata !DIExpression()), !dbg !1466
  %71 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %11, i32 0, i32 0, !dbg !1467
  store i32 1, i32* %71, align 4, !dbg !1467, !tbaa !489
  %72 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %11, i32 0, i32 1, !dbg !1467
  store %struct.iovec* %10, %struct.iovec** %72, align 4, !dbg !1467, !tbaa !491
  %73 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %11, i32 0, i32 2, !dbg !1467
  store i32 0, i32* %73, align 4, !dbg !1467, !tbaa !492
  %74 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %11, i32 0, i32 3, !dbg !1467
  store i32* null, i32** %74, align 4, !dbg !1467, !tbaa !493
  %75 = load i32, i32* %6, align 4, !dbg !1468, !tbaa !359
  %76 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 1, !dbg !1469
  %77 = load i32, i32* %76, align 4, !dbg !1469, !tbaa !621
  %78 = call arm_aapcscc i32 @read_msg(i32 %75, i32 %77, i32 0, %struct.ipc_msg* %11), !dbg !1470
  store i32 %78, i32* %8, align 4, !dbg !1471, !tbaa !359
  %79 = load i32, i32* %6, align 4, !dbg !1472, !tbaa !359
  %80 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 1, !dbg !1473
  %81 = load i32, i32* %80, align 4, !dbg !1473, !tbaa !621
  %82 = call arm_aapcscc i32 @put_msg(i32 %79, i32 %81), !dbg !1474
  %83 = load i32, i32* %8, align 4, !dbg !1475, !tbaa !359
  %84 = icmp slt i32 %83, 0, !dbg !1477
  br i1 %84, label %85, label %100, !dbg !1478

85:                                               ; preds = %63
  br label %86, !dbg !1479

86:                                               ; preds = %85
  br label %87, !dbg !1481

87:                                               ; preds = %86
  %88 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1485, !tbaa !432
  %89 = load i32, i32* %8, align 4, !dbg !1485, !tbaa !359
  %90 = load i32, i32* %6, align 4, !dbg !1485, !tbaa !359
  %91 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %88, i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.38, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 167, i32 %89, i32 %90), !dbg !1485
  %92 = load i32, i32* %8, align 4, !dbg !1485, !tbaa !359
  %93 = load i32, i32* %6, align 4, !dbg !1485, !tbaa !359
  %94 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([37 x i8], [37 x i8]* @.str.38, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 167, i32 %92, i32 %93), !dbg !1485
  br label %95, !dbg !1485

95:                                               ; preds = %87
  br label %96, !dbg !1485

96:                                               ; preds = %95
  br label %97, !dbg !1487

97:                                               ; preds = %96
  br label %98, !dbg !1487

98:                                               ; preds = %97
  %99 = load i32, i32* %8, align 4, !dbg !1488, !tbaa !359
  store i32 %99, i32* %3, align 4, !dbg !1489
  store i32 1, i32* %9, align 4
  br label %132, !dbg !1489

100:                                              ; preds = %63
  %101 = load i32, i32* %8, align 4, !dbg !1490, !tbaa !359
  %102 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 0, !dbg !1492
  %103 = load i32, i32* %102, align 4, !dbg !1492, !tbaa !605
  %104 = icmp ult i32 %101, %103, !dbg !1493
  br i1 %104, label %105, label %119, !dbg !1494

105:                                              ; preds = %100
  br label %106, !dbg !1495

106:                                              ; preds = %105
  br label %107, !dbg !1497

107:                                              ; preds = %106
  %108 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1501, !tbaa !432
  %109 = load i32, i32* %8, align 4, !dbg !1501, !tbaa !359
  %110 = load i32, i32* %6, align 4, !dbg !1501, !tbaa !359
  %111 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %108, i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.39, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 172, i32 %109, i32 %110), !dbg !1501
  %112 = load i32, i32* %8, align 4, !dbg !1501, !tbaa !359
  %113 = load i32, i32* %6, align 4, !dbg !1501, !tbaa !359
  %114 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([42 x i8], [42 x i8]* @.str.39, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 172, i32 %112, i32 %113), !dbg !1501
  br label %115, !dbg !1501

115:                                              ; preds = %107
  br label %116, !dbg !1501

116:                                              ; preds = %115
  br label %117, !dbg !1503

117:                                              ; preds = %116
  br label %118, !dbg !1503

118:                                              ; preds = %117
  store i32 -7, i32* %3, align 4, !dbg !1504
  store i32 1, i32* %9, align 4
  br label %132, !dbg !1504

119:                                              ; preds = %100
  %120 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %4, align 4, !dbg !1505, !tbaa !432
  %121 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %120, i32 0, i32 1, !dbg !1506
  %122 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %121, i32 0, i32 0, !dbg !1507
  %123 = load i32 (%struct.ipc_channel_context*, i8*, i32)*, i32 (%struct.ipc_channel_context*, i8*, i32)** %122, align 4, !dbg !1507, !tbaa !452
  %124 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %4, align 4, !dbg !1508, !tbaa !432
  %125 = load i8*, i8** @msg_buf, align 4, !dbg !1509, !tbaa !432
  %126 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %7, i32 0, i32 0, !dbg !1510
  %127 = load i32, i32* %126, align 4, !dbg !1510, !tbaa !605
  %128 = call arm_aapcscc i32 %123(%struct.ipc_channel_context* %124, i8* %125, i32 %127), !dbg !1505
  store i32 %128, i32* %8, align 4, !dbg !1511, !tbaa !359
  br label %129, !dbg !1512

129:                                              ; preds = %119
  call void @llvm.dbg.label(metadata !1409), !dbg !1513
  br label %130, !dbg !1512

130:                                              ; preds = %129
  call void @llvm.dbg.label(metadata !1410), !dbg !1514
  %131 = load i32, i32* %8, align 4, !dbg !1515, !tbaa !359
  store i32 %131, i32* %3, align 4, !dbg !1516
  store i32 1, i32* %9, align 4
  br label %132, !dbg !1516

132:                                              ; preds = %130, %118, %98
  %133 = bitcast %struct.ipc_msg* %11 to i8*, !dbg !1517
  call void @llvm.lifetime.end.p0i8(i64 16, i8* %133) #6, !dbg !1517
  %134 = bitcast %struct.iovec* %10 to i8*, !dbg !1517
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %134) #6, !dbg !1517
  br label %135

135:                                              ; preds = %132, %58, %39, %22
  %136 = bitcast i32* %8 to i8*, !dbg !1517
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %136) #6, !dbg !1517
  %137 = bitcast %struct.ipc_msg_info* %7 to i8*, !dbg !1517
  call void @llvm.lifetime.end.p0i8(i64 12, i8* %137) #6, !dbg !1517
  %138 = bitcast i32* %6 to i8*, !dbg !1517
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %138) #6, !dbg !1517
  %139 = load i32, i32* %3, align 4, !dbg !1517
  ret i32 %139, !dbg !1517
}

; Function Attrs: nounwind sspstrong
define internal arm_aapcscc void @do_disconnect(%struct.ipc_channel_context* %0, %struct.uevent* %1) #0 !dbg !1518 {
  %3 = alloca %struct.ipc_channel_context*, align 4
  %4 = alloca %struct.uevent*, align 4
  store %struct.ipc_channel_context* %0, %struct.ipc_channel_context** %3, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %3, metadata !1522, metadata !DIExpression()), !dbg !1524
  store %struct.uevent* %1, %struct.uevent** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %4, metadata !1523, metadata !DIExpression()), !dbg !1525
  %5 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1526, !tbaa !432
  %6 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %5, i32 0, i32 2, !dbg !1527
  call arm_aapcscc void @list_delete(%struct.list_node* %6), !dbg !1528
  %7 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1529, !tbaa !432
  %8 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %7, i32 0, i32 1, !dbg !1530
  %9 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %8, i32 0, i32 1, !dbg !1531
  %10 = load void (%struct.ipc_channel_context*)*, void (%struct.ipc_channel_context*)** %9, align 4, !dbg !1531, !tbaa !443
  %11 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1532, !tbaa !432
  call arm_aapcscc void %10(%struct.ipc_channel_context* %11), !dbg !1529
  %12 = load %struct.uevent*, %struct.uevent** %4, align 4, !dbg !1533, !tbaa !432
  %13 = getelementptr inbounds %struct.uevent, %struct.uevent* %12, i32 0, i32 0, !dbg !1534
  %14 = load i32, i32* %13, align 4, !dbg !1534, !tbaa !374
  %15 = call arm_aapcscc i32 @close(i32 %14), !dbg !1535
  ret void, !dbg !1536
}

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc void @list_delete(%struct.list_node* %0) #4 !dbg !1537 {
  %2 = alloca %struct.list_node*, align 4
  store %struct.list_node* %0, %struct.list_node** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.list_node** %2, metadata !1539, metadata !DIExpression()), !dbg !1540
  %3 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1541, !tbaa !432
  %4 = getelementptr inbounds %struct.list_node, %struct.list_node* %3, i32 0, i32 0, !dbg !1542
  %5 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1542, !tbaa !1085
  %6 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1543, !tbaa !432
  %7 = getelementptr inbounds %struct.list_node, %struct.list_node* %6, i32 0, i32 1, !dbg !1544
  %8 = load %struct.list_node*, %struct.list_node** %7, align 4, !dbg !1544, !tbaa !1081
  %9 = getelementptr inbounds %struct.list_node, %struct.list_node* %8, i32 0, i32 0, !dbg !1545
  store %struct.list_node* %5, %struct.list_node** %9, align 4, !dbg !1546, !tbaa !1085
  %10 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1547, !tbaa !432
  %11 = getelementptr inbounds %struct.list_node, %struct.list_node* %10, i32 0, i32 1, !dbg !1548
  %12 = load %struct.list_node*, %struct.list_node** %11, align 4, !dbg !1548, !tbaa !1081
  %13 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1549, !tbaa !432
  %14 = getelementptr inbounds %struct.list_node, %struct.list_node* %13, i32 0, i32 0, !dbg !1550
  %15 = load %struct.list_node*, %struct.list_node** %14, align 4, !dbg !1550, !tbaa !1085
  %16 = getelementptr inbounds %struct.list_node, %struct.list_node* %15, i32 0, i32 1, !dbg !1551
  store %struct.list_node* %12, %struct.list_node** %16, align 4, !dbg !1552, !tbaa !1081
  %17 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1553, !tbaa !432
  %18 = getelementptr inbounds %struct.list_node, %struct.list_node* %17, i32 0, i32 1, !dbg !1554
  store %struct.list_node* null, %struct.list_node** %18, align 4, !dbg !1555, !tbaa !1081
  %19 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1556, !tbaa !432
  %20 = getelementptr inbounds %struct.list_node, %struct.list_node* %19, i32 0, i32 0, !dbg !1557
  store %struct.list_node* null, %struct.list_node** %20, align 4, !dbg !1558, !tbaa !1085
  ret void, !dbg !1559
}

; Function Attrs: noreturn
declare dso_local arm_aapcscc void @abort() #5

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @ipc_port_destroy(%struct.ipc_port_context* %0) #0 !dbg !1560 {
  %2 = alloca %struct.ipc_port_context*, align 4
  %3 = alloca %struct.ipc_channel_context*, align 4
  %4 = alloca %struct.list_node*, align 4
  %5 = alloca %struct.ipc_channel_context*, align 4
  %6 = alloca %struct.ipc_channel_context*, align 4
  %7 = alloca i32, align 4
  %8 = alloca i8*, align 4
  %9 = alloca i8, align 1
  store %struct.ipc_port_context* %0, %struct.ipc_port_context** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_port_context** %2, metadata !1564, metadata !DIExpression()), !dbg !1573
  %10 = load %struct.ipc_port_context*, %struct.ipc_port_context** %2, align 4, !dbg !1574, !tbaa !432
  %11 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %10, i32 0, i32 0, !dbg !1575
  %12 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %11, i32 0, i32 1, !dbg !1576
  %13 = load i32, i32* %12, align 4, !dbg !1576, !tbaa !989
  %14 = call arm_aapcscc i32 @close(i32 %13), !dbg !1577
  br label %15, !dbg !1578

15:                                               ; preds = %87, %1
  %16 = load %struct.ipc_port_context*, %struct.ipc_port_context** %2, align 4, !dbg !1579, !tbaa !432
  %17 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %16, i32 0, i32 2, !dbg !1580
  %18 = call arm_aapcscc zeroext i1 @list_is_empty(%struct.list_node* %17), !dbg !1581
  %19 = xor i1 %18, true, !dbg !1582
  br i1 %19, label %20, label %93, !dbg !1578

20:                                               ; preds = %15
  %21 = bitcast %struct.ipc_channel_context** %3 to i8*, !dbg !1583
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %21) #6, !dbg !1583
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %3, metadata !1565, metadata !DIExpression()), !dbg !1584
  %22 = bitcast %struct.list_node** %4 to i8*, !dbg !1585
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %22) #6, !dbg !1585
  call void @llvm.dbg.declare(metadata %struct.list_node** %4, metadata !1567, metadata !DIExpression()), !dbg !1585
  %23 = load %struct.ipc_port_context*, %struct.ipc_port_context** %2, align 4, !dbg !1585, !tbaa !432
  %24 = getelementptr inbounds %struct.ipc_port_context, %struct.ipc_port_context* %23, i32 0, i32 2, !dbg !1585
  %25 = call arm_aapcscc %struct.list_node* @list_remove_head(%struct.list_node* %24), !dbg !1585
  store %struct.list_node* %25, %struct.list_node** %4, align 4, !dbg !1585, !tbaa !432
  %26 = bitcast %struct.ipc_channel_context** %5 to i8*, !dbg !1585
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %26) #6, !dbg !1585
  call void @llvm.dbg.declare(metadata %struct.ipc_channel_context** %5, metadata !1569, metadata !DIExpression()), !dbg !1585
  %27 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1586, !tbaa !432
  %28 = icmp ne %struct.list_node* %27, null, !dbg !1586
  br i1 %28, label %29, label %34, !dbg !1585

29:                                               ; preds = %20
  %30 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1586, !tbaa !432
  %31 = ptrtoint %struct.list_node* %30 to i32, !dbg !1586
  %32 = sub i32 %31, 16, !dbg !1586
  %33 = inttoptr i32 %32 to %struct.ipc_channel_context*, !dbg !1586
  store %struct.ipc_channel_context* %33, %struct.ipc_channel_context** %5, align 4, !dbg !1586, !tbaa !432
  br label %35, !dbg !1586

34:                                               ; preds = %20
  store %struct.ipc_channel_context* null, %struct.ipc_channel_context** %5, align 4, !dbg !1586, !tbaa !432
  br label %35

35:                                               ; preds = %34, %29
  %36 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %5, align 4, !dbg !1585, !tbaa !432
  store %struct.ipc_channel_context* %36, %struct.ipc_channel_context** %6, align 4, !dbg !1586, !tbaa !432
  %37 = bitcast %struct.ipc_channel_context** %5 to i8*, !dbg !1588
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %37) #6, !dbg !1588
  %38 = bitcast %struct.list_node** %4 to i8*, !dbg !1588
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %38) #6, !dbg !1588
  %39 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %6, align 4, !dbg !1585, !tbaa !432
  store %struct.ipc_channel_context* %39, %struct.ipc_channel_context** %3, align 4, !dbg !1584, !tbaa !432
  %40 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1589, !tbaa !432
  %41 = icmp ne %struct.ipc_channel_context* %40, null, !dbg !1589
  br i1 %41, label %44, label %42, !dbg !1589

42:                                               ; preds = %35
  call arm_aapcscc void @__assert_fail(i8* getelementptr inbounds ([9 x i8], [9 x i8]* @.str.18, i32 0, i32 0), i8* getelementptr inbounds ([91 x i8], [91 x i8]* @.str.3, i32 0, i32 0), i32 421, i8* getelementptr inbounds ([17 x i8], [17 x i8]* @__func__.ipc_port_destroy, i32 0, i32 0)) #7, !dbg !1589
  unreachable, !dbg !1589

43:                                               ; No predecessors!
  br label %44, !dbg !1589

44:                                               ; preds = %43, %35
  %45 = phi i1 [ true, %35 ], [ false, %43 ]
  %46 = zext i1 %45 to i32, !dbg !1589
  %47 = bitcast i32* %7 to i8*, !dbg !1590
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %47) #6, !dbg !1590
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1570, metadata !DIExpression()), !dbg !1591
  %48 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1592, !tbaa !432
  %49 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %48, i32 0, i32 0, !dbg !1593
  %50 = getelementptr inbounds %struct.ipc_context, %struct.ipc_context* %49, i32 0, i32 1, !dbg !1594
  %51 = load i32, i32* %50, align 4, !dbg !1594, !tbaa !499
  store i32 %51, i32* %7, align 4, !dbg !1591, !tbaa !359
  br label %52, !dbg !1595

52:                                               ; preds = %44
  br label %53, !dbg !1596

53:                                               ; preds = %52
  %54 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1600, !tbaa !432
  %55 = load i32, i32* %7, align 4, !dbg !1600, !tbaa !359
  %56 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %54, i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.19, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 423, i32 %55), !dbg !1600
  %57 = load i32, i32* %7, align 4, !dbg !1600, !tbaa !359
  %58 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([43 x i8], [43 x i8]* @.str.19, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 423, i32 %57), !dbg !1600
  br label %59, !dbg !1600

59:                                               ; preds = %53
  br label %60, !dbg !1600

60:                                               ; preds = %59
  br label %61, !dbg !1602

61:                                               ; preds = %60
  br label %62, !dbg !1602

62:                                               ; preds = %61
  %63 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1603, !tbaa !432
  %64 = getelementptr inbounds %struct.ipc_channel_context, %struct.ipc_channel_context* %63, i32 0, i32 1, !dbg !1604
  %65 = getelementptr inbounds %struct.ipc_channel_ops, %struct.ipc_channel_ops* %64, i32 0, i32 1, !dbg !1605
  %66 = load void (%struct.ipc_channel_context*)*, void (%struct.ipc_channel_context*)** %65, align 4, !dbg !1605, !tbaa !443
  %67 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1606, !tbaa !432
  call arm_aapcscc void %66(%struct.ipc_channel_context* %67), !dbg !1603
  %68 = bitcast i8** %8 to i8*, !dbg !1607
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %68) #6, !dbg !1607
  call void @llvm.dbg.declare(metadata i8** %8, metadata !1571, metadata !DIExpression()), !dbg !1608
  %69 = load %struct.ipc_channel_context*, %struct.ipc_channel_context** %3, align 4, !dbg !1609, !tbaa !432
  %70 = bitcast %struct.ipc_channel_context* %69 to i8*, !dbg !1610
  %71 = getelementptr inbounds i8, i8* %70, i32 24, !dbg !1611
  %72 = getelementptr inbounds i8, i8* %71, i32 1, !dbg !1612
  store i8* %72, i8** %8, align 4, !dbg !1608, !tbaa !432
  call void @llvm.lifetime.start.p0i8(i64 1, i8* %9) #6, !dbg !1613
  call void @llvm.dbg.declare(metadata i8* %9, metadata !1572, metadata !DIExpression()), !dbg !1614
  %73 = load i8*, i8** %8, align 4, !dbg !1615, !tbaa !432
  %74 = load i8, i8* %73, align 1, !dbg !1616, !tbaa !1617
  store i8 %74, i8* %9, align 1, !dbg !1614, !tbaa !1617
  br label %75, !dbg !1618

75:                                               ; preds = %62
  br label %76, !dbg !1619

76:                                               ; preds = %75
  %77 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1623, !tbaa !432
  %78 = load i8, i8* %9, align 1, !dbg !1623, !tbaa !1617
  %79 = zext i8 %78 to i32, !dbg !1623
  %80 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %77, i8* getelementptr inbounds ([28 x i8], [28 x i8]* @.str.20, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 427, i32 %79), !dbg !1623
  %81 = load i8, i8* %9, align 1, !dbg !1623, !tbaa !1617
  %82 = zext i8 %81 to i32, !dbg !1623
  %83 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([28 x i8], [28 x i8]* @.str.20, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 427, i32 %82), !dbg !1623
  br label %84, !dbg !1623

84:                                               ; preds = %76
  br label %85, !dbg !1623

85:                                               ; preds = %84
  br label %86, !dbg !1625

86:                                               ; preds = %85
  br label %87, !dbg !1625

87:                                               ; preds = %86
  %88 = load i32, i32* %7, align 4, !dbg !1626, !tbaa !359
  %89 = call arm_aapcscc i32 @close(i32 %88), !dbg !1627
  call void @llvm.lifetime.end.p0i8(i64 1, i8* %9) #6, !dbg !1628
  %90 = bitcast i8** %8 to i8*, !dbg !1628
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %90) #6, !dbg !1628
  %91 = bitcast i32* %7 to i8*, !dbg !1628
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %91) #6, !dbg !1628
  %92 = bitcast %struct.ipc_channel_context** %3 to i8*, !dbg !1628
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %92) #6, !dbg !1628
  br label %15, !dbg !1578, !llvm.loop !1629

93:                                               ; preds = %15
  ret i32 0, !dbg !1630
}

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc zeroext i1 @list_is_empty(%struct.list_node* %0) #4 !dbg !1631 {
  %2 = alloca %struct.list_node*, align 4
  store %struct.list_node* %0, %struct.list_node** %2, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.list_node** %2, metadata !1635, metadata !DIExpression()), !dbg !1636
  %3 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1637, !tbaa !432
  %4 = getelementptr inbounds %struct.list_node, %struct.list_node* %3, i32 0, i32 1, !dbg !1638
  %5 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1638, !tbaa !1081
  %6 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1639, !tbaa !432
  %7 = icmp eq %struct.list_node* %5, %6, !dbg !1640
  %8 = zext i1 %7 to i64, !dbg !1641
  %9 = select i1 %7, i32 1, i32 0, !dbg !1641
  %10 = icmp ne i32 %9, 0, !dbg !1641
  ret i1 %10, !dbg !1642
}

; Function Attrs: inlinehint nounwind sspstrong
define internal arm_aapcscc %struct.list_node* @list_remove_head(%struct.list_node* %0) #4 !dbg !1643 {
  %2 = alloca %struct.list_node*, align 4
  %3 = alloca %struct.list_node*, align 4
  %4 = alloca %struct.list_node*, align 4
  store %struct.list_node* %0, %struct.list_node** %3, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.list_node** %3, metadata !1647, metadata !DIExpression()), !dbg !1651
  %5 = load %struct.list_node*, %struct.list_node** %3, align 4, !dbg !1652, !tbaa !432
  %6 = getelementptr inbounds %struct.list_node, %struct.list_node* %5, i32 0, i32 1, !dbg !1653
  %7 = load %struct.list_node*, %struct.list_node** %6, align 4, !dbg !1653, !tbaa !1081
  %8 = load %struct.list_node*, %struct.list_node** %3, align 4, !dbg !1654, !tbaa !432
  %9 = icmp ne %struct.list_node* %7, %8, !dbg !1655
  br i1 %9, label %10, label %18, !dbg !1656

10:                                               ; preds = %1
  %11 = bitcast %struct.list_node** %4 to i8*, !dbg !1657
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %11) #6, !dbg !1657
  call void @llvm.dbg.declare(metadata %struct.list_node** %4, metadata !1648, metadata !DIExpression()), !dbg !1658
  %12 = load %struct.list_node*, %struct.list_node** %3, align 4, !dbg !1659, !tbaa !432
  %13 = getelementptr inbounds %struct.list_node, %struct.list_node* %12, i32 0, i32 1, !dbg !1660
  %14 = load %struct.list_node*, %struct.list_node** %13, align 4, !dbg !1660, !tbaa !1081
  store %struct.list_node* %14, %struct.list_node** %4, align 4, !dbg !1658, !tbaa !432
  %15 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1661, !tbaa !432
  call arm_aapcscc void @list_delete(%struct.list_node* %15), !dbg !1662
  %16 = load %struct.list_node*, %struct.list_node** %4, align 4, !dbg !1663, !tbaa !432
  store %struct.list_node* %16, %struct.list_node** %2, align 4, !dbg !1664
  %17 = bitcast %struct.list_node** %4 to i8*, !dbg !1665
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %17) #6, !dbg !1665
  br label %19

18:                                               ; preds = %1
  store %struct.list_node* null, %struct.list_node** %2, align 4, !dbg !1666
  br label %19, !dbg !1666

19:                                               ; preds = %18, %10
  %20 = load %struct.list_node*, %struct.list_node** %2, align 4, !dbg !1668
  ret %struct.list_node* %20, !dbg !1668
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc void @ipc_loop() #0 !dbg !1669 {
  %1 = alloca i32, align 4
  %2 = alloca %struct.uevent, align 4
  %3 = bitcast i32* %1 to i8*, !dbg !1675
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %3) #6, !dbg !1675
  call void @llvm.dbg.declare(metadata i32* %1, metadata !1673, metadata !DIExpression()), !dbg !1676
  %4 = bitcast %struct.uevent* %2 to i8*, !dbg !1677
  call void @llvm.lifetime.start.p0i8(i64 12, i8* %4) #6, !dbg !1677
  call void @llvm.dbg.declare(metadata %struct.uevent* %2, metadata !1674, metadata !DIExpression()), !dbg !1678
  br label %5, !dbg !1679

5:                                                ; preds = %29, %0
  br label %6, !dbg !1679

6:                                                ; preds = %5
  %7 = getelementptr inbounds %struct.uevent, %struct.uevent* %2, i32 0, i32 0, !dbg !1680
  store i32 -1, i32* %7, align 4, !dbg !1682, !tbaa !374
  %8 = getelementptr inbounds %struct.uevent, %struct.uevent* %2, i32 0, i32 1, !dbg !1683
  store i32 0, i32* %8, align 4, !dbg !1684, !tbaa !379
  %9 = getelementptr inbounds %struct.uevent, %struct.uevent* %2, i32 0, i32 2, !dbg !1685
  store i8* null, i8** %9, align 4, !dbg !1686, !tbaa !382
  %10 = call arm_aapcscc i32 @wait_any(%struct.uevent* %2, i32 -1), !dbg !1687
  store i32 %10, i32* %1, align 4, !dbg !1688, !tbaa !359
  %11 = load i32, i32* %1, align 4, !dbg !1689, !tbaa !359
  %12 = icmp slt i32 %11, 0, !dbg !1691
  br i1 %12, label %13, label %25, !dbg !1692

13:                                               ; preds = %6
  br label %14, !dbg !1693

14:                                               ; preds = %13
  br label %15, !dbg !1695

15:                                               ; preds = %14
  %16 = load %struct._IO_FILE*, %struct._IO_FILE** @stderr, align 4, !dbg !1699, !tbaa !432
  %17 = load i32, i32* %1, align 4, !dbg !1699, !tbaa !359
  %18 = call arm_aapcscc i32 (%struct._IO_FILE*, i8*, ...) @fprintf(%struct._IO_FILE* %16, i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str.21, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 444, i32 %17), !dbg !1699
  %19 = load i32, i32* %1, align 4, !dbg !1699, !tbaa !359
  %20 = call arm_aapcscc i32 (i8*, ...) @unittest_printf(i8* getelementptr inbounds ([30 x i8], [30 x i8]* @.str.21, i32 0, i32 0), i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str.1.2, i32 0, i32 0), i32 444, i32 %19), !dbg !1699
  br label %21, !dbg !1699

21:                                               ; preds = %15
  br label %22, !dbg !1699

22:                                               ; preds = %21
  br label %23, !dbg !1701

23:                                               ; preds = %22
  br label %24, !dbg !1701

24:                                               ; preds = %23
  br label %30, !dbg !1702

25:                                               ; preds = %6
  %26 = load i32, i32* %1, align 4, !dbg !1703, !tbaa !359
  %27 = icmp eq i32 %26, 0, !dbg !1705
  br i1 %27, label %28, label %29, !dbg !1706

28:                                               ; preds = %25
  call arm_aapcscc void @dispatch_event(%struct.uevent* %2), !dbg !1707
  br label %29, !dbg !1709

29:                                               ; preds = %28, %25
  br label %5, !dbg !1679, !llvm.loop !1710

30:                                               ; preds = %24
  %31 = bitcast %struct.uevent* %2 to i8*, !dbg !1712
  call void @llvm.lifetime.end.p0i8(i64 12, i8* %31) #6, !dbg !1712
  %32 = bitcast i32* %1 to i8*, !dbg !1712
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %32) #6, !dbg !1712
  ret void, !dbg !1712
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @get_msg(i32 %0, %struct.ipc_msg_info* %1) #0 !dbg !1713 {
  %3 = alloca i32, align 4
  %4 = alloca %struct.ipc_msg_info*, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !1724, metadata !DIExpression()), !dbg !1729
  store %struct.ipc_msg_info* %1, %struct.ipc_msg_info** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_msg_info** %4, metadata !1725, metadata !DIExpression()), !dbg !1730
  %8 = load i32, i32* %3, align 4, !dbg !1731, !tbaa !359
  %9 = bitcast i32* %5 to i8*, !dbg !1732
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %9) #6, !dbg !1732
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1726, metadata !DIExpression()), !dbg !1733
  %10 = call arm_aapcscc i32 @nd_get_msg_ret(), !dbg !1734
  store i32 %10, i32* %5, align 4, !dbg !1733, !tbaa !359
  %11 = bitcast i32* %6 to i8*, !dbg !1735
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %11) #6, !dbg !1735
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1727, metadata !DIExpression()), !dbg !1736
  %12 = call arm_aapcscc i32 @nd_msg_len(), !dbg !1737
  store i32 %12, i32* %6, align 4, !dbg !1736, !tbaa !359
  %13 = bitcast i32* %7 to i8*, !dbg !1738
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %13) #6, !dbg !1738
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1728, metadata !DIExpression()), !dbg !1739
  %14 = call arm_aapcscc i32 @nd_msg_id(), !dbg !1740
  store i32 %14, i32* %7, align 4, !dbg !1739, !tbaa !359
  %15 = load i32, i32* %5, align 4, !dbg !1741, !tbaa !359
  %16 = icmp eq i32 %15, 0, !dbg !1743
  br i1 %16, label %17, label %23, !dbg !1744

17:                                               ; preds = %2
  %18 = load i32, i32* %6, align 4, !dbg !1745, !tbaa !359
  %19 = icmp ugt i32 %18, 0, !dbg !1747
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %19), !dbg !1748
  %20 = load i32, i32* %7, align 4, !dbg !1749, !tbaa !359
  %21 = icmp ugt i32 %20, 0, !dbg !1750
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %21), !dbg !1751
  %22 = load i32, i32* %7, align 4, !dbg !1752, !tbaa !359
  store i32 %22, i32* @cur_msg_id, align 4, !dbg !1753, !tbaa !359
  store i8 0, i8* @cur_msg_retired, align 1, !dbg !1754, !tbaa !1755
  br label %24, !dbg !1757

23:                                               ; preds = %2
  store i32 0, i32* %6, align 4, !dbg !1758, !tbaa !359
  store i32 0, i32* %7, align 4, !dbg !1760, !tbaa !359
  br label %24

24:                                               ; preds = %23, %17
  %25 = load i32, i32* %6, align 4, !dbg !1761, !tbaa !359
  %26 = load %struct.ipc_msg_info*, %struct.ipc_msg_info** %4, align 4, !dbg !1762, !tbaa !432
  %27 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %26, i32 0, i32 0, !dbg !1763
  store i32 %25, i32* %27, align 4, !dbg !1764, !tbaa !605
  %28 = load i32, i32* %7, align 4, !dbg !1765, !tbaa !359
  %29 = load %struct.ipc_msg_info*, %struct.ipc_msg_info** %4, align 4, !dbg !1766, !tbaa !432
  %30 = getelementptr inbounds %struct.ipc_msg_info, %struct.ipc_msg_info* %29, i32 0, i32 1, !dbg !1767
  store i32 %28, i32* %30, align 4, !dbg !1768, !tbaa !621
  %31 = load i32, i32* %5, align 4, !dbg !1769, !tbaa !359
  %32 = bitcast i32* %7 to i8*, !dbg !1770
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %32) #6, !dbg !1770
  %33 = bitcast i32* %6 to i8*, !dbg !1770
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %33) #6, !dbg !1770
  %34 = bitcast i32* %5 to i8*, !dbg !1770
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %34) #6, !dbg !1770
  ret i32 %31, !dbg !1771
}

declare !dbg !165 dso_local arm_aapcscc i32 @nd_get_msg_ret() #3

declare !dbg !169 dso_local arm_aapcscc i32 @nd_msg_len() #3

declare !dbg !172 dso_local arm_aapcscc i32 @nd_msg_id() #3

declare dso_local arm_aapcscc void @__VERIFIER_assume(i1 zeroext) #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @read_msg(i32 %0, i32 %1, i32 %2, %struct.ipc_msg* %3) #0 !dbg !1772 {
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  %8 = alloca %struct.ipc_msg*, align 4
  %9 = alloca i32, align 4
  %10 = alloca %struct.iovec*, align 4
  %11 = alloca i32, align 4
  %12 = alloca i32, align 4
  %13 = alloca %struct.iovec, align 4
  store i32 %0, i32* %5, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1790, metadata !DIExpression()), !dbg !1804
  store i32 %1, i32* %6, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1791, metadata !DIExpression()), !dbg !1805
  store i32 %2, i32* %7, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1792, metadata !DIExpression()), !dbg !1806
  store %struct.ipc_msg* %3, %struct.ipc_msg** %8, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_msg** %8, metadata !1793, metadata !DIExpression()), !dbg !1807
  %14 = load i32, i32* %5, align 4, !dbg !1808, !tbaa !359
  %15 = load i32, i32* %7, align 4, !dbg !1809, !tbaa !359
  %16 = bitcast i32* %9 to i8*, !dbg !1810
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %16) #6, !dbg !1810
  call void @llvm.dbg.declare(metadata i32* %9, metadata !1794, metadata !DIExpression()), !dbg !1811
  %17 = call arm_aapcscc i32 @nd_read_msg_ret(), !dbg !1812
  store i32 %17, i32* %9, align 4, !dbg !1811, !tbaa !359
  %18 = bitcast %struct.iovec** %10 to i8*, !dbg !1813
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %18) #6, !dbg !1813
  call void @llvm.dbg.declare(metadata %struct.iovec** %10, metadata !1795, metadata !DIExpression()), !dbg !1814
  %19 = load %struct.ipc_msg*, %struct.ipc_msg** %8, align 4, !dbg !1815, !tbaa !432
  %20 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %19, i32 0, i32 1, !dbg !1816
  %21 = load %struct.iovec*, %struct.iovec** %20, align 4, !dbg !1816, !tbaa !491
  store %struct.iovec* %21, %struct.iovec** %10, align 4, !dbg !1814, !tbaa !432
  %22 = bitcast i32* %11 to i8*, !dbg !1817
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %22) #6, !dbg !1817
  call void @llvm.dbg.declare(metadata i32* %11, metadata !1796, metadata !DIExpression()), !dbg !1818
  %23 = load %struct.ipc_msg*, %struct.ipc_msg** %8, align 4, !dbg !1819, !tbaa !432
  %24 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %23, i32 0, i32 0, !dbg !1820
  %25 = load i32, i32* %24, align 4, !dbg !1820, !tbaa !489
  store i32 %25, i32* %11, align 4, !dbg !1818, !tbaa !359
  %26 = load i32, i32* %9, align 4, !dbg !1821, !tbaa !359
  %27 = icmp sge i32 %26, 0, !dbg !1822
  br i1 %27, label %28, label %57, !dbg !1823

28:                                               ; preds = %4
  %29 = bitcast i32* %12 to i8*, !dbg !1824
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %29) #6, !dbg !1824
  call void @llvm.dbg.declare(metadata i32* %12, metadata !1797, metadata !DIExpression()), !dbg !1825
  store i32 0, i32* %12, align 4, !dbg !1825, !tbaa !359
  br label %30, !dbg !1824

30:                                               ; preds = %53, %28
  %31 = load i32, i32* %12, align 4, !dbg !1826, !tbaa !359
  %32 = load i32, i32* %11, align 4, !dbg !1827, !tbaa !359
  %33 = icmp ult i32 %31, %32, !dbg !1828
  br i1 %33, label %36, label %34, !dbg !1829

34:                                               ; preds = %30
  %35 = bitcast i32* %12 to i8*, !dbg !1830
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %35) #6, !dbg !1830
  br label %56

36:                                               ; preds = %30
  %37 = bitcast %struct.iovec* %13 to i8*, !dbg !1831
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %37) #6, !dbg !1831
  call void @llvm.dbg.declare(metadata %struct.iovec* %13, metadata !1801, metadata !DIExpression()), !dbg !1832
  %38 = load %struct.iovec*, %struct.iovec** %10, align 4, !dbg !1833, !tbaa !432
  %39 = load i32, i32* %12, align 4, !dbg !1834, !tbaa !359
  %40 = getelementptr inbounds %struct.iovec, %struct.iovec* %38, i32 %39, !dbg !1833
  %41 = bitcast %struct.iovec* %13 to i8*, !dbg !1833
  %42 = bitcast %struct.iovec* %40 to i8*, !dbg !1833
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* align 4 %41, i8* align 4 %42, i32 8, i1 false), !dbg !1833, !tbaa.struct !1835
  %43 = getelementptr inbounds %struct.iovec, %struct.iovec* %13, i32 0, i32 0, !dbg !1836
  %44 = load i8*, i8** %43, align 4, !dbg !1836, !tbaa !482
  %45 = getelementptr inbounds %struct.iovec, %struct.iovec* %13, i32 0, i32 1, !dbg !1836
  %46 = load i32, i32* %45, align 4, !dbg !1836, !tbaa !485
  %47 = call arm_aapcscc zeroext i1 @sea_is_dereferenceable(i8* %44, i32 %46), !dbg !1836
  br i1 %47, label %49, label %48, !dbg !1836

48:                                               ; preds = %36
  call arm_aapcscc void @__VERIFIER_error(), !dbg !1836
  br label %49, !dbg !1836

49:                                               ; preds = %48, %36
  %50 = phi i1 [ true, %36 ], [ false, %48 ]
  %51 = zext i1 %50 to i32, !dbg !1836
  %52 = bitcast %struct.iovec* %13 to i8*, !dbg !1837
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %52) #6, !dbg !1837
  br label %53, !dbg !1838

53:                                               ; preds = %49
  %54 = load i32, i32* %12, align 4, !dbg !1839, !tbaa !359
  %55 = add i32 %54, 1, !dbg !1839
  store i32 %55, i32* %12, align 4, !dbg !1839, !tbaa !359
  br label %30, !dbg !1830, !llvm.loop !1840

56:                                               ; preds = %34
  br label %57, !dbg !1842

57:                                               ; preds = %56, %4
  %58 = load i32, i32* %9, align 4, !dbg !1843, !tbaa !359
  %59 = bitcast i32* %11 to i8*, !dbg !1844
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %59) #6, !dbg !1844
  %60 = bitcast %struct.iovec** %10 to i8*, !dbg !1844
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %60) #6, !dbg !1844
  %61 = bitcast i32* %9 to i8*, !dbg !1844
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %61) #6, !dbg !1844
  ret i32 %58, !dbg !1845
}

declare !dbg !173 dso_local arm_aapcscc i32 @nd_read_msg_ret() #3

declare !dbg !174 dso_local arm_aapcscc zeroext i1 @sea_is_dereferenceable(i8*, i32) #3

declare dso_local arm_aapcscc void @__VERIFIER_error() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @send_msg(i32 %0, %struct.ipc_msg* %1) #0 !dbg !1846 {
  %3 = alloca i32, align 4
  %4 = alloca %struct.ipc_msg*, align 4
  %5 = alloca i32, align 4
  %6 = alloca %struct.iovec*, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca %struct.iovec, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !1850, metadata !DIExpression()), !dbg !1862
  store %struct.ipc_msg* %1, %struct.ipc_msg** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.ipc_msg** %4, metadata !1851, metadata !DIExpression()), !dbg !1863
  %10 = load i32, i32* %3, align 4, !dbg !1864, !tbaa !359
  %11 = bitcast i32* %5 to i8*, !dbg !1865
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %11) #6, !dbg !1865
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1852, metadata !DIExpression()), !dbg !1866
  %12 = call arm_aapcscc i32 @nd_send_msg_ret(), !dbg !1867
  store i32 %12, i32* %5, align 4, !dbg !1866, !tbaa !359
  %13 = bitcast %struct.iovec** %6 to i8*, !dbg !1868
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %13) #6, !dbg !1868
  call void @llvm.dbg.declare(metadata %struct.iovec** %6, metadata !1853, metadata !DIExpression()), !dbg !1869
  %14 = load %struct.ipc_msg*, %struct.ipc_msg** %4, align 4, !dbg !1870, !tbaa !432
  %15 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %14, i32 0, i32 1, !dbg !1871
  %16 = load %struct.iovec*, %struct.iovec** %15, align 4, !dbg !1871, !tbaa !491
  store %struct.iovec* %16, %struct.iovec** %6, align 4, !dbg !1869, !tbaa !432
  %17 = bitcast i32* %7 to i8*, !dbg !1872
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %17) #6, !dbg !1872
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1854, metadata !DIExpression()), !dbg !1873
  %18 = load %struct.ipc_msg*, %struct.ipc_msg** %4, align 4, !dbg !1874, !tbaa !432
  %19 = getelementptr inbounds %struct.ipc_msg, %struct.ipc_msg* %18, i32 0, i32 0, !dbg !1875
  %20 = load i32, i32* %19, align 4, !dbg !1875, !tbaa !489
  store i32 %20, i32* %7, align 4, !dbg !1873, !tbaa !359
  %21 = load i32, i32* %5, align 4, !dbg !1876, !tbaa !359
  %22 = icmp sge i32 %21, 0, !dbg !1877
  br i1 %22, label %23, label %52, !dbg !1878

23:                                               ; preds = %2
  %24 = bitcast i32* %8 to i8*, !dbg !1879
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %24) #6, !dbg !1879
  call void @llvm.dbg.declare(metadata i32* %8, metadata !1855, metadata !DIExpression()), !dbg !1880
  store i32 0, i32* %8, align 4, !dbg !1880, !tbaa !359
  br label %25, !dbg !1879

25:                                               ; preds = %48, %23
  %26 = load i32, i32* %8, align 4, !dbg !1881, !tbaa !359
  %27 = load i32, i32* %7, align 4, !dbg !1882, !tbaa !359
  %28 = icmp ult i32 %26, %27, !dbg !1883
  br i1 %28, label %31, label %29, !dbg !1884

29:                                               ; preds = %25
  %30 = bitcast i32* %8 to i8*, !dbg !1885
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %30) #6, !dbg !1885
  br label %51

31:                                               ; preds = %25
  %32 = bitcast %struct.iovec* %9 to i8*, !dbg !1886
  call void @llvm.lifetime.start.p0i8(i64 8, i8* %32) #6, !dbg !1886
  call void @llvm.dbg.declare(metadata %struct.iovec* %9, metadata !1859, metadata !DIExpression()), !dbg !1887
  %33 = load %struct.iovec*, %struct.iovec** %6, align 4, !dbg !1888, !tbaa !432
  %34 = load i32, i32* %8, align 4, !dbg !1889, !tbaa !359
  %35 = getelementptr inbounds %struct.iovec, %struct.iovec* %33, i32 %34, !dbg !1888
  %36 = bitcast %struct.iovec* %9 to i8*, !dbg !1888
  %37 = bitcast %struct.iovec* %35 to i8*, !dbg !1888
  call void @llvm.memcpy.p0i8.p0i8.i32(i8* align 4 %36, i8* align 4 %37, i32 8, i1 false), !dbg !1888, !tbaa.struct !1835
  %38 = getelementptr inbounds %struct.iovec, %struct.iovec* %9, i32 0, i32 0, !dbg !1890
  %39 = load i8*, i8** %38, align 4, !dbg !1890, !tbaa !482
  %40 = getelementptr inbounds %struct.iovec, %struct.iovec* %9, i32 0, i32 1, !dbg !1890
  %41 = load i32, i32* %40, align 4, !dbg !1890, !tbaa !485
  %42 = call arm_aapcscc zeroext i1 @sea_is_dereferenceable(i8* %39, i32 %41), !dbg !1890
  br i1 %42, label %44, label %43, !dbg !1890

43:                                               ; preds = %31
  call arm_aapcscc void @__VERIFIER_error(), !dbg !1890
  br label %44, !dbg !1890

44:                                               ; preds = %43, %31
  %45 = phi i1 [ true, %31 ], [ false, %43 ]
  %46 = zext i1 %45 to i32, !dbg !1890
  %47 = bitcast %struct.iovec* %9 to i8*, !dbg !1891
  call void @llvm.lifetime.end.p0i8(i64 8, i8* %47) #6, !dbg !1891
  br label %48, !dbg !1892

48:                                               ; preds = %44
  %49 = load i32, i32* %8, align 4, !dbg !1893, !tbaa !359
  %50 = add i32 %49, 1, !dbg !1893
  store i32 %50, i32* %8, align 4, !dbg !1893, !tbaa !359
  br label %25, !dbg !1885, !llvm.loop !1894

51:                                               ; preds = %29
  br label %52, !dbg !1896

52:                                               ; preds = %51, %2
  %53 = load i32, i32* %5, align 4, !dbg !1897, !tbaa !359
  %54 = bitcast i32* %7 to i8*, !dbg !1898
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %54) #6, !dbg !1898
  %55 = bitcast %struct.iovec** %6 to i8*, !dbg !1898
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %55) #6, !dbg !1898
  %56 = bitcast i32* %5 to i8*, !dbg !1898
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %56) #6, !dbg !1898
  ret i32 %53, !dbg !1899
}

declare !dbg !179 dso_local arm_aapcscc i32 @nd_send_msg_ret() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @put_msg(i32 %0, i32 %1) #0 !dbg !1900 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !1904, metadata !DIExpression()), !dbg !1906
  store i32 %1, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !1905, metadata !DIExpression()), !dbg !1907
  %5 = load i32, i32* %3, align 4, !dbg !1908, !tbaa !359
  %6 = load i32, i32* @cur_msg_id, align 4, !dbg !1909, !tbaa !359
  %7 = load i32, i32* %4, align 4, !dbg !1910, !tbaa !359
  %8 = icmp eq i32 %6, %7, !dbg !1911
  %9 = zext i1 %8 to i8, !dbg !1912
  store i8 %9, i8* @cur_msg_retired, align 1, !dbg !1912, !tbaa !1755
  %10 = call arm_aapcscc i32 @nd_put_msg_ret(), !dbg !1913
  ret i32 %10, !dbg !1914
}

declare !dbg !180 dso_local arm_aapcscc i32 @nd_put_msg_ret() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @wait(i32 %0, %struct.uevent* %1, i32 %2) #0 !dbg !1915 {
  %4 = alloca i32, align 4
  %5 = alloca %struct.uevent*, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store i32 %0, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !1926, metadata !DIExpression()), !dbg !1930
  store %struct.uevent* %1, %struct.uevent** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %5, metadata !1927, metadata !DIExpression()), !dbg !1931
  store i32 %2, i32* %6, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1928, metadata !DIExpression()), !dbg !1932
  %8 = load i32, i32* %6, align 4, !dbg !1933, !tbaa !359
  %9 = bitcast i32* %7 to i8*, !dbg !1934
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %9) #6, !dbg !1934
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1929, metadata !DIExpression()), !dbg !1935
  %10 = call arm_aapcscc i32 @nd_wait_ret(), !dbg !1936
  store i32 %10, i32* %7, align 4, !dbg !1935, !tbaa !359
  %11 = load i32, i32* %7, align 4, !dbg !1937, !tbaa !359
  %12 = icmp eq i32 %11, 0, !dbg !1939
  br i1 %12, label %13, label %30, !dbg !1940

13:                                               ; preds = %3
  %14 = load i32, i32* %4, align 4, !dbg !1941, !tbaa !359
  %15 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1943, !tbaa !432
  %16 = getelementptr inbounds %struct.uevent, %struct.uevent* %15, i32 0, i32 0, !dbg !1944
  store i32 %14, i32* %16, align 4, !dbg !1945, !tbaa !374
  %17 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1946, !tbaa !432
  %18 = getelementptr inbounds %struct.uevent, %struct.uevent* %17, i32 0, i32 0, !dbg !1947
  %19 = load i32, i32* %18, align 4, !dbg !1947, !tbaa !374
  %20 = call arm_aapcscc i8* @get_handle_cookie(i32 %19), !dbg !1948
  %21 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1949, !tbaa !432
  %22 = getelementptr inbounds %struct.uevent, %struct.uevent* %21, i32 0, i32 2, !dbg !1950
  store i8* %20, i8** %22, align 4, !dbg !1951, !tbaa !382
  %23 = call arm_aapcscc i32 @nd_event_flag(), !dbg !1952
  %24 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1953, !tbaa !432
  %25 = getelementptr inbounds %struct.uevent, %struct.uevent* %24, i32 0, i32 1, !dbg !1954
  store i32 %23, i32* %25, align 4, !dbg !1955, !tbaa !379
  %26 = load %struct.uevent*, %struct.uevent** %5, align 4, !dbg !1956, !tbaa !432
  %27 = getelementptr inbounds %struct.uevent, %struct.uevent* %26, i32 0, i32 1, !dbg !1957
  %28 = load i32, i32* %27, align 4, !dbg !1957, !tbaa !379
  %29 = icmp ult i32 %28, 22, !dbg !1958
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %29), !dbg !1959
  br label %30, !dbg !1960

30:                                               ; preds = %13, %3
  %31 = load i32, i32* %7, align 4, !dbg !1961, !tbaa !359
  %32 = bitcast i32* %7 to i8*, !dbg !1962
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %32) #6, !dbg !1962
  ret i32 %31, !dbg !1963
}

declare !dbg !181 dso_local arm_aapcscc i32 @nd_wait_ret() #3

declare !dbg !186 dso_local arm_aapcscc i32 @nd_event_flag() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @wait_any(%struct.uevent* %0, i32 %1) #0 !dbg !1964 {
  %3 = alloca %struct.uevent*, align 4
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  %7 = alloca i32, align 4
  store %struct.uevent* %0, %struct.uevent** %3, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uevent** %3, metadata !1968, metadata !DIExpression()), !dbg !1973
  store i32 %1, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !1969, metadata !DIExpression()), !dbg !1974
  %8 = load i32, i32* %4, align 4, !dbg !1975, !tbaa !359
  %9 = bitcast i32* %5 to i8*, !dbg !1976
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %9) #6, !dbg !1976
  call void @llvm.dbg.declare(metadata i32* %5, metadata !1970, metadata !DIExpression()), !dbg !1977
  %10 = bitcast i32* %6 to i8*, !dbg !1978
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %10) #6, !dbg !1978
  call void @llvm.dbg.declare(metadata i32* %6, metadata !1971, metadata !DIExpression()), !dbg !1979
  %11 = call arm_aapcscc zeroext i1 @is_current_chan_active(), !dbg !1980
  br i1 %11, label %12, label %14, !dbg !1982

12:                                               ; preds = %2
  %13 = call arm_aapcscc i32 @get_current_chan_handle(), !dbg !1983
  store i32 %13, i32* %5, align 4, !dbg !1985, !tbaa !359
  br label %26, !dbg !1986

14:                                               ; preds = %2
  %15 = call arm_aapcscc zeroext i1 @is_secure_port_active(), !dbg !1987
  br i1 %15, label %16, label %18, !dbg !1989

16:                                               ; preds = %14
  %17 = call arm_aapcscc i32 @get_secure_port_handle(), !dbg !1990
  store i32 %17, i32* %5, align 4, !dbg !1992, !tbaa !359
  br label %25, !dbg !1993

18:                                               ; preds = %14
  %19 = call arm_aapcscc zeroext i1 @is_non_secure_port_active(), !dbg !1994
  br i1 %19, label %20, label %22, !dbg !1996

20:                                               ; preds = %18
  %21 = call arm_aapcscc i32 @get_non_secure_port_handle(), !dbg !1997
  store i32 %21, i32* %5, align 4, !dbg !1999, !tbaa !359
  br label %24, !dbg !2000

22:                                               ; preds = %18
  %23 = call arm_aapcscc i32 @nd_wait_handle(), !dbg !2001
  store i32 %23, i32* %5, align 4, !dbg !2003, !tbaa !359
  br label %24

24:                                               ; preds = %22, %20
  br label %25

25:                                               ; preds = %24, %16
  br label %26

26:                                               ; preds = %25, %12
  %27 = load i32, i32* %5, align 4, !dbg !2004, !tbaa !359
  %28 = load %struct.uevent*, %struct.uevent** %3, align 4, !dbg !2005, !tbaa !432
  %29 = getelementptr inbounds %struct.uevent, %struct.uevent* %28, i32 0, i32 0, !dbg !2006
  store i32 %27, i32* %29, align 4, !dbg !2007, !tbaa !374
  %30 = load %struct.uevent*, %struct.uevent** %3, align 4, !dbg !2008, !tbaa !432
  %31 = getelementptr inbounds %struct.uevent, %struct.uevent* %30, i32 0, i32 0, !dbg !2009
  %32 = load i32, i32* %31, align 4, !dbg !2009, !tbaa !374
  %33 = call arm_aapcscc i8* @get_handle_cookie(i32 %32), !dbg !2010
  %34 = load %struct.uevent*, %struct.uevent** %3, align 4, !dbg !2011, !tbaa !432
  %35 = getelementptr inbounds %struct.uevent, %struct.uevent* %34, i32 0, i32 2, !dbg !2012
  store i8* %33, i8** %35, align 4, !dbg !2013, !tbaa !382
  %36 = call arm_aapcscc i32 @nd_event_flag(), !dbg !2014
  store i32 %36, i32* %6, align 4, !dbg !2015, !tbaa !359
  %37 = load i32, i32* %6, align 4, !dbg !2016, !tbaa !359
  %38 = icmp ult i32 %37, 22, !dbg !2017
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %38), !dbg !2018
  %39 = load i32, i32* %6, align 4, !dbg !2019, !tbaa !359
  %40 = load %struct.uevent*, %struct.uevent** %3, align 4, !dbg !2020, !tbaa !432
  %41 = getelementptr inbounds %struct.uevent, %struct.uevent* %40, i32 0, i32 1, !dbg !2021
  store i32 %39, i32* %41, align 4, !dbg !2022, !tbaa !379
  %42 = bitcast i32* %7 to i8*, !dbg !2023
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %42) #6, !dbg !2023
  call void @llvm.dbg.declare(metadata i32* %7, metadata !1972, metadata !DIExpression()), !dbg !2024
  %43 = call arm_aapcscc i32 @nd_wait_any_ret(), !dbg !2025
  store i32 %43, i32* %7, align 4, !dbg !2024, !tbaa !359
  %44 = load i32, i32* %7, align 4, !dbg !2026, !tbaa !359
  %45 = icmp sle i32 %44, 0, !dbg !2027
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %45), !dbg !2028
  %46 = load i32, i32* %7, align 4, !dbg !2029, !tbaa !359
  %47 = bitcast i32* %7 to i8*, !dbg !2030
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %47) #6, !dbg !2030
  %48 = bitcast i32* %6 to i8*, !dbg !2030
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %48) #6, !dbg !2030
  %49 = bitcast i32* %5 to i8*, !dbg !2030
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %49) #6, !dbg !2030
  ret i32 %46, !dbg !2031
}

declare !dbg !195 dso_local arm_aapcscc i32 @nd_wait_handle() #3

declare !dbg !196 dso_local arm_aapcscc i32 @nd_wait_any_ret() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @port_create(i8* %0, i32 %1, i32 %2, i32 %3) #0 !dbg !2032 {
  %5 = alloca i32, align 4
  %6 = alloca i8*, align 4
  %7 = alloca i32, align 4
  %8 = alloca i32, align 4
  %9 = alloca i32, align 4
  %10 = alloca i32, align 4
  %11 = alloca i32, align 4
  store i8* %0, i8** %6, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata i8** %6, metadata !2036, metadata !DIExpression()), !dbg !2041
  store i32 %1, i32* %7, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %7, metadata !2037, metadata !DIExpression()), !dbg !2042
  store i32 %2, i32* %8, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %8, metadata !2038, metadata !DIExpression()), !dbg !2043
  store i32 %3, i32* %9, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %9, metadata !2039, metadata !DIExpression()), !dbg !2044
  %12 = load i8*, i8** %6, align 4, !dbg !2045, !tbaa !432
  %13 = load i32, i32* %7, align 4, !dbg !2046, !tbaa !359
  %14 = load i32, i32* %8, align 4, !dbg !2047, !tbaa !359
  %15 = bitcast i32* %10 to i8*, !dbg !2048
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %15) #6, !dbg !2048
  call void @llvm.dbg.declare(metadata i32* %10, metadata !2040, metadata !DIExpression()), !dbg !2049
  %16 = call arm_aapcscc i32 @nd_port_handle(), !dbg !2050
  store i32 %16, i32* %10, align 4, !dbg !2049, !tbaa !359
  %17 = load i32, i32* %10, align 4, !dbg !2051, !tbaa !359
  %18 = icmp slt i32 %17, 0, !dbg !2053
  br i1 %18, label %19, label %21, !dbg !2054

19:                                               ; preds = %4
  %20 = load i32, i32* %10, align 4, !dbg !2055, !tbaa !359
  store i32 %20, i32* %5, align 4, !dbg !2056
  store i32 1, i32* %11, align 4
  br label %49, !dbg !2056

21:                                               ; preds = %4
  %22 = load i32, i32* %10, align 4, !dbg !2057, !tbaa !359
  %23 = or i32 %22, 2, !dbg !2057
  store i32 %23, i32* %10, align 4, !dbg !2057, !tbaa !359
  %24 = load i32, i32* %9, align 4, !dbg !2058, !tbaa !359
  %25 = and i32 %24, 1, !dbg !2060
  %26 = icmp ne i32 %25, 0, !dbg !2060
  br i1 %26, label %27, label %34, !dbg !2061

27:                                               ; preds = %21
  %28 = load i32, i32* %9, align 4, !dbg !2062, !tbaa !359
  %29 = and i32 %28, 2, !dbg !2063
  %30 = icmp ne i32 %29, 0, !dbg !2063
  br i1 %30, label %34, label %31, !dbg !2064

31:                                               ; preds = %27
  %32 = load i32, i32* %10, align 4, !dbg !2065, !tbaa !359
  %33 = or i32 %32, 1, !dbg !2065
  store i32 %33, i32* %10, align 4, !dbg !2065, !tbaa !359
  br label %46, !dbg !2067

34:                                               ; preds = %27, %21
  %35 = load i32, i32* %9, align 4, !dbg !2068, !tbaa !359
  %36 = and i32 %35, 1, !dbg !2070
  %37 = icmp ne i32 %36, 0, !dbg !2070
  br i1 %37, label %45, label %38, !dbg !2071

38:                                               ; preds = %34
  %39 = load i32, i32* %9, align 4, !dbg !2072, !tbaa !359
  %40 = and i32 %39, 2, !dbg !2073
  %41 = icmp ne i32 %40, 0, !dbg !2073
  br i1 %41, label %42, label %45, !dbg !2074

42:                                               ; preds = %38
  %43 = load i32, i32* %10, align 4, !dbg !2075, !tbaa !359
  %44 = and i32 %43, -2, !dbg !2075
  store i32 %44, i32* %10, align 4, !dbg !2075, !tbaa !359
  br label %45, !dbg !2077

45:                                               ; preds = %42, %38, %34
  br label %46

46:                                               ; preds = %45, %31
  %47 = load i32, i32* %10, align 4, !dbg !2078, !tbaa !359
  call arm_aapcscc void @add_handle(i32 %47), !dbg !2079
  %48 = load i32, i32* %10, align 4, !dbg !2080, !tbaa !359
  store i32 %48, i32* %5, align 4, !dbg !2081
  store i32 1, i32* %11, align 4
  br label %49, !dbg !2081

49:                                               ; preds = %46, %19
  %50 = bitcast i32* %10 to i8*, !dbg !2082
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %50) #6, !dbg !2082
  %51 = load i32, i32* %5, align 4, !dbg !2082
  ret i32 %51, !dbg !2082
}

declare !dbg !197 dso_local arm_aapcscc i32 @nd_port_handle() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @set_cookie(i32 %0, i8* %1) #0 !dbg !2083 {
  %3 = alloca i32, align 4
  %4 = alloca i32, align 4
  %5 = alloca i8*, align 4
  %6 = alloca i32, align 4
  store i32 %0, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2087, metadata !DIExpression()), !dbg !2090
  store i8* %1, i8** %5, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata i8** %5, metadata !2088, metadata !DIExpression()), !dbg !2091
  %7 = load i32, i32* %4, align 4, !dbg !2092, !tbaa !359
  %8 = call arm_aapcscc zeroext i1 @contains_handle(i32 %7), !dbg !2094
  br i1 %8, label %10, label %9, !dbg !2095

9:                                                ; preds = %2
  store i32 -1, i32* %3, align 4, !dbg !2096
  br label %23, !dbg !2096

10:                                               ; preds = %2
  %11 = bitcast i32* %6 to i8*, !dbg !2098
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %11) #6, !dbg !2098
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2089, metadata !DIExpression()), !dbg !2099
  %12 = call arm_aapcscc i32 @nd_set_cookie_ret(), !dbg !2100
  store i32 %12, i32* %6, align 4, !dbg !2099, !tbaa !359
  %13 = load i32, i32* %6, align 4, !dbg !2101, !tbaa !359
  %14 = icmp sle i32 %13, 0, !dbg !2102
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %14), !dbg !2103
  %15 = load i32, i32* %6, align 4, !dbg !2104, !tbaa !359
  %16 = icmp eq i32 %15, 0, !dbg !2106
  br i1 %16, label %17, label %20, !dbg !2107

17:                                               ; preds = %10
  %18 = load i32, i32* %4, align 4, !dbg !2108, !tbaa !359
  %19 = load i8*, i8** %5, align 4, !dbg !2110, !tbaa !432
  call arm_aapcscc void @set_handle_cookie(i32 %18, i8* %19), !dbg !2111
  br label %20, !dbg !2112

20:                                               ; preds = %17, %10
  %21 = load i32, i32* %6, align 4, !dbg !2113, !tbaa !359
  store i32 %21, i32* %3, align 4, !dbg !2114
  %22 = bitcast i32* %6 to i8*, !dbg !2115
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %22) #6, !dbg !2115
  br label %23

23:                                               ; preds = %20, %9
  %24 = load i32, i32* %3, align 4, !dbg !2115
  ret i32 %24, !dbg !2115
}

declare !dbg !204 dso_local arm_aapcscc i32 @nd_set_cookie_ret() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @accept(i32 %0, %struct.uuid* %1) #0 !dbg !2116 {
  %3 = alloca i32, align 4
  %4 = alloca %struct.uuid*, align 4
  %5 = alloca i32, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2128, metadata !DIExpression()), !dbg !2131
  store %struct.uuid* %1, %struct.uuid** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata %struct.uuid** %4, metadata !2129, metadata !DIExpression()), !dbg !2132
  %6 = load i32, i32* %3, align 4, !dbg !2133, !tbaa !359
  %7 = bitcast i32* %5 to i8*, !dbg !2134
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %7) #6, !dbg !2134
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2130, metadata !DIExpression()), !dbg !2135
  %8 = call arm_aapcscc i32 @nd_chan_handle(), !dbg !2136
  store i32 %8, i32* %5, align 4, !dbg !2135, !tbaa !359
  %9 = load i32, i32* %5, align 4, !dbg !2137, !tbaa !359
  %10 = icmp sge i32 %9, 0, !dbg !2139
  br i1 %10, label %11, label %26, !dbg !2140

11:                                               ; preds = %2
  %12 = load i32, i32* %5, align 4, !dbg !2141, !tbaa !359
  %13 = and i32 %12, 2, !dbg !2143
  %14 = icmp ne i32 %13, 0, !dbg !2144
  %15 = xor i1 %14, true, !dbg !2144
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %15), !dbg !2145
  %16 = call arm_aapcscc i32 @nd_time_low(), !dbg !2146
  %17 = load %struct.uuid*, %struct.uuid** %4, align 4, !dbg !2147, !tbaa !432
  %18 = getelementptr inbounds %struct.uuid, %struct.uuid* %17, i32 0, i32 0, !dbg !2148
  store i32 %16, i32* %18, align 4, !dbg !2149, !tbaa !2150
  %19 = call arm_aapcscc zeroext i16 @nd_time_mid(), !dbg !2153
  %20 = load %struct.uuid*, %struct.uuid** %4, align 4, !dbg !2154, !tbaa !432
  %21 = getelementptr inbounds %struct.uuid, %struct.uuid* %20, i32 0, i32 1, !dbg !2155
  store i16 %19, i16* %21, align 4, !dbg !2156, !tbaa !2157
  %22 = call arm_aapcscc zeroext i16 @nd_time_hi_n_ver(), !dbg !2158
  %23 = load %struct.uuid*, %struct.uuid** %4, align 4, !dbg !2159, !tbaa !432
  %24 = getelementptr inbounds %struct.uuid, %struct.uuid* %23, i32 0, i32 2, !dbg !2160
  store i16 %22, i16* %24, align 2, !dbg !2161, !tbaa !2162
  %25 = load i32, i32* %5, align 4, !dbg !2163, !tbaa !359
  call arm_aapcscc void @add_handle(i32 %25), !dbg !2164
  br label %26, !dbg !2165

26:                                               ; preds = %11, %2
  %27 = load i32, i32* %5, align 4, !dbg !2166, !tbaa !359
  %28 = bitcast i32* %5 to i8*, !dbg !2167
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %28) #6, !dbg !2167
  ret i32 %27, !dbg !2168
}

declare !dbg !208 dso_local arm_aapcscc i32 @nd_chan_handle() #3

declare !dbg !209 dso_local arm_aapcscc i32 @nd_time_low() #3

declare !dbg !210 dso_local arm_aapcscc zeroext i16 @nd_time_mid() #3

declare !dbg !213 dso_local arm_aapcscc zeroext i16 @nd_time_hi_n_ver() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @close(i32 %0) #0 !dbg !2169 {
  %2 = alloca i32, align 4
  %3 = alloca i32, align 4
  store i32 %0, i32* %2, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2173, metadata !DIExpression()), !dbg !2175
  %4 = bitcast i32* %3 to i8*, !dbg !2176
  call void @llvm.lifetime.start.p0i8(i64 4, i8* %4) #6, !dbg !2176
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2174, metadata !DIExpression()), !dbg !2177
  %5 = call arm_aapcscc i32 @nd_close_ret(), !dbg !2178
  store i32 %5, i32* %3, align 4, !dbg !2177, !tbaa !359
  %6 = load i32, i32* %3, align 4, !dbg !2179, !tbaa !359
  %7 = icmp sle i32 %6, 0, !dbg !2180
  call arm_aapcscc void @__VERIFIER_assume(i1 zeroext %7), !dbg !2181
  %8 = load i32, i32* %2, align 4, !dbg !2182, !tbaa !359
  call arm_aapcscc void @remove_handle(i32 %8), !dbg !2183
  %9 = load i32, i32* %3, align 4, !dbg !2184, !tbaa !359
  %10 = bitcast i32* %3 to i8*, !dbg !2185
  call void @llvm.lifetime.end.p0i8(i64 4, i8* %10) #6, !dbg !2185
  ret i32 %9, !dbg !2186
}

declare !dbg !214 dso_local arm_aapcscc i32 @nd_close_ret() #3

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i8* @realloc(i8* %0, i32 %1) #0 !dbg !2187 {
  %3 = alloca i8*, align 4
  %4 = alloca i32, align 4
  store i8* %0, i8** %3, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata i8** %3, metadata !2192, metadata !DIExpression()), !dbg !2194
  store i32 %1, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2193, metadata !DIExpression()), !dbg !2195
  %5 = load i8*, i8** %3, align 4, !dbg !2196, !tbaa !432
  %6 = icmp ne i8* %5, null, !dbg !2196
  br i1 %6, label %7, label %9, !dbg !2198

7:                                                ; preds = %2
  %8 = load i8*, i8** %3, align 4, !dbg !2199, !tbaa !432
  call arm_aapcscc void @free(i8* %8), !dbg !2201
  br label %9, !dbg !2202

9:                                                ; preds = %7, %2
  %10 = load i32, i32* %4, align 4, !dbg !2203, !tbaa !359
  %11 = call arm_aapcscc i8* @malloc(i32 %10), !dbg !2204
  store i8* %11, i8** %3, align 4, !dbg !2205, !tbaa !432
  %12 = load i8*, i8** %3, align 4, !dbg !2206, !tbaa !432
  ret i8* %12, !dbg !2207
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc void @handle_table_init(i32 %0, i32 %1, i32 %2) #0 !dbg !2208 {
  %4 = alloca i32, align 4
  %5 = alloca i32, align 4
  %6 = alloca i32, align 4
  store i32 %0, i32* %4, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %4, metadata !2212, metadata !DIExpression()), !dbg !2215
  store i32 %1, i32* %5, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %5, metadata !2213, metadata !DIExpression()), !dbg !2216
  store i32 %2, i32* %6, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %6, metadata !2214, metadata !DIExpression()), !dbg !2217
  %7 = load i32, i32* %4, align 4, !dbg !2218, !tbaa !359
  store i32 %7, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 0), align 4, !dbg !2219, !tbaa !2220
  %8 = load i32, i32* %4, align 4, !dbg !2222, !tbaa !359
  %9 = icmp ne i32 %8, -1, !dbg !2223
  %10 = zext i1 %9 to i8, !dbg !2224
  store i8 %10, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 1), align 4, !dbg !2224, !tbaa !2225
  %11 = load i32, i32* %5, align 4, !dbg !2226, !tbaa !359
  store i32 %11, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 3), align 4, !dbg !2227, !tbaa !2228
  %12 = load i32, i32* %5, align 4, !dbg !2229, !tbaa !359
  %13 = icmp ne i32 %12, -1, !dbg !2230
  %14 = zext i1 %13 to i8, !dbg !2231
  store i8 %14, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 4), align 4, !dbg !2231, !tbaa !2232
  %15 = load i32, i32* %6, align 4, !dbg !2233, !tbaa !359
  store i32 %15, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 6), align 4, !dbg !2234, !tbaa !2235
  %16 = load i32, i32* %6, align 4, !dbg !2236, !tbaa !359
  %17 = icmp ne i32 %16, -1, !dbg !2237
  %18 = zext i1 %17 to i8, !dbg !2238
  store i8 %18, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 7), align 4, !dbg !2238, !tbaa !2239
  ret void, !dbg !2240
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc void @add_handle(i32 %0) #0 !dbg !2241 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2245, metadata !DIExpression()), !dbg !2246
  %3 = load i32, i32* %2, align 4, !dbg !2247, !tbaa !359
  %4 = and i32 %3, 2, !dbg !2247
  %5 = icmp ne i32 %4, 0, !dbg !2247
  br i1 %5, label %6, label %15, !dbg !2249

6:                                                ; preds = %1
  %7 = load i32, i32* %2, align 4, !dbg !2250, !tbaa !359
  %8 = and i32 %7, 1, !dbg !2250
  %9 = icmp ne i32 %8, 0, !dbg !2250
  br i1 %9, label %10, label %12, !dbg !2253

10:                                               ; preds = %6
  %11 = load i32, i32* %2, align 4, !dbg !2254, !tbaa !359
  store i32 %11, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 0), align 4, !dbg !2256, !tbaa !2220
  store i8 1, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 1), align 4, !dbg !2257, !tbaa !2225
  br label %14, !dbg !2258

12:                                               ; preds = %6
  %13 = load i32, i32* %2, align 4, !dbg !2259, !tbaa !359
  store i32 %13, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 3), align 4, !dbg !2261, !tbaa !2228
  store i8 1, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 4), align 4, !dbg !2262, !tbaa !2232
  br label %14

14:                                               ; preds = %12, %10
  br label %17, !dbg !2263

15:                                               ; preds = %1
  %16 = load i32, i32* %2, align 4, !dbg !2264, !tbaa !359
  store i32 %16, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 6), align 4, !dbg !2266, !tbaa !2235
  store i8 1, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 7), align 4, !dbg !2267, !tbaa !2239
  br label %17

17:                                               ; preds = %15, %14
  ret void, !dbg !2268
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc void @remove_handle(i32 %0) #0 !dbg !2269 {
  %2 = alloca i32, align 4
  store i32 %0, i32* %2, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %2, metadata !2271, metadata !DIExpression()), !dbg !2272
  %3 = load i32, i32* %2, align 4, !dbg !2273, !tbaa !359
  %4 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 0), align 4, !dbg !2275, !tbaa !2220
  %5 = icmp eq i32 %3, %4, !dbg !2276
  br i1 %5, label %6, label %7, !dbg !2277

6:                                                ; preds = %1
  store i8 0, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 1), align 4, !dbg !2278, !tbaa !2225
  br label %19, !dbg !2280

7:                                                ; preds = %1
  %8 = load i32, i32* %2, align 4, !dbg !2281, !tbaa !359
  %9 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 3), align 4, !dbg !2283, !tbaa !2228
  %10 = icmp eq i32 %8, %9, !dbg !2284
  br i1 %10, label %11, label %12, !dbg !2285

11:                                               ; preds = %7
  store i8 0, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 4), align 4, !dbg !2286, !tbaa !2232
  br label %18, !dbg !2288

12:                                               ; preds = %7
  %13 = load i32, i32* %2, align 4, !dbg !2289, !tbaa !359
  %14 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 6), align 4, !dbg !2291, !tbaa !2235
  %15 = icmp eq i32 %13, %14, !dbg !2292
  br i1 %15, label %16, label %17, !dbg !2293

16:                                               ; preds = %12
  store i8 0, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 7), align 4, !dbg !2294, !tbaa !2239
  br label %17, !dbg !2296

17:                                               ; preds = %16, %12
  br label %18

18:                                               ; preds = %17, %11
  br label %19

19:                                               ; preds = %18, %6
  ret void, !dbg !2297
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc zeroext i1 @contains_handle(i32 %0) #0 !dbg !2298 {
  %2 = alloca i1, align 1
  %3 = alloca i32, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2302, metadata !DIExpression()), !dbg !2303
  %4 = load i32, i32* %3, align 4, !dbg !2304, !tbaa !359
  %5 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 0), align 4, !dbg !2306, !tbaa !2220
  %6 = icmp eq i32 %4, %5, !dbg !2307
  br i1 %6, label %7, label %10, !dbg !2308

7:                                                ; preds = %1
  %8 = load i8, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 1), align 4, !dbg !2309, !tbaa !2225, !range !2311
  %9 = trunc i8 %8 to i1, !dbg !2309
  store i1 %9, i1* %2, align 1, !dbg !2312
  br label %27, !dbg !2312

10:                                               ; preds = %1
  %11 = load i32, i32* %3, align 4, !dbg !2313, !tbaa !359
  %12 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 3), align 4, !dbg !2315, !tbaa !2228
  %13 = icmp eq i32 %11, %12, !dbg !2316
  br i1 %13, label %14, label %17, !dbg !2317

14:                                               ; preds = %10
  %15 = load i8, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 4), align 4, !dbg !2318, !tbaa !2232, !range !2311
  %16 = trunc i8 %15 to i1, !dbg !2318
  store i1 %16, i1* %2, align 1, !dbg !2320
  br label %27, !dbg !2320

17:                                               ; preds = %10
  %18 = load i32, i32* %3, align 4, !dbg !2321, !tbaa !359
  %19 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 6), align 4, !dbg !2323, !tbaa !2235
  %20 = icmp eq i32 %18, %19, !dbg !2324
  br i1 %20, label %21, label %24, !dbg !2325

21:                                               ; preds = %17
  %22 = load i8, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 7), align 4, !dbg !2326, !tbaa !2239, !range !2311
  %23 = trunc i8 %22 to i1, !dbg !2326
  store i1 %23, i1* %2, align 1, !dbg !2328
  br label %27, !dbg !2328

24:                                               ; preds = %17
  br label %25

25:                                               ; preds = %24
  br label %26

26:                                               ; preds = %25
  store i1 false, i1* %2, align 1, !dbg !2329
  br label %27, !dbg !2329

27:                                               ; preds = %26, %21, %14, %7
  %28 = load i1, i1* %2, align 1, !dbg !2330
  ret i1 %28, !dbg !2330
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i8* @get_handle_cookie(i32 %0) #0 !dbg !2331 {
  %2 = alloca i8*, align 4
  %3 = alloca i32, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2335, metadata !DIExpression()), !dbg !2336
  %4 = load i32, i32* %3, align 4, !dbg !2337, !tbaa !359
  %5 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 0), align 4, !dbg !2339, !tbaa !2220
  %6 = icmp eq i32 %4, %5, !dbg !2340
  br i1 %6, label %7, label %9, !dbg !2341

7:                                                ; preds = %1
  %8 = load i8*, i8** getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 2), align 4, !dbg !2342, !tbaa !2344
  store i8* %8, i8** %2, align 4, !dbg !2345
  br label %24, !dbg !2345

9:                                                ; preds = %1
  %10 = load i32, i32* %3, align 4, !dbg !2346, !tbaa !359
  %11 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 3), align 4, !dbg !2348, !tbaa !2228
  %12 = icmp eq i32 %10, %11, !dbg !2349
  br i1 %12, label %13, label %15, !dbg !2350

13:                                               ; preds = %9
  %14 = load i8*, i8** getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 5), align 4, !dbg !2351, !tbaa !2353
  store i8* %14, i8** %2, align 4, !dbg !2354
  br label %24, !dbg !2354

15:                                               ; preds = %9
  %16 = load i32, i32* %3, align 4, !dbg !2355, !tbaa !359
  %17 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 6), align 4, !dbg !2357, !tbaa !2235
  %18 = icmp eq i32 %16, %17, !dbg !2358
  br i1 %18, label %19, label %21, !dbg !2359

19:                                               ; preds = %15
  %20 = load i8*, i8** getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 8), align 4, !dbg !2360, !tbaa !2362
  store i8* %20, i8** %2, align 4, !dbg !2363
  br label %24, !dbg !2363

21:                                               ; preds = %15
  br label %22

22:                                               ; preds = %21
  br label %23

23:                                               ; preds = %22
  store i8* null, i8** %2, align 4, !dbg !2364
  br label %24, !dbg !2364

24:                                               ; preds = %23, %19, %13, %7
  %25 = load i8*, i8** %2, align 4, !dbg !2365
  ret i8* %25, !dbg !2365
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc void @set_handle_cookie(i32 %0, i8* %1) #0 !dbg !2366 {
  %3 = alloca i32, align 4
  %4 = alloca i8*, align 4
  store i32 %0, i32* %3, align 4, !tbaa !359
  call void @llvm.dbg.declare(metadata i32* %3, metadata !2370, metadata !DIExpression()), !dbg !2372
  store i8* %1, i8** %4, align 4, !tbaa !432
  call void @llvm.dbg.declare(metadata i8** %4, metadata !2371, metadata !DIExpression()), !dbg !2373
  %5 = load i32, i32* %3, align 4, !dbg !2374, !tbaa !359
  %6 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 0), align 4, !dbg !2376, !tbaa !2220
  %7 = icmp eq i32 %5, %6, !dbg !2377
  br i1 %7, label %8, label %10, !dbg !2378

8:                                                ; preds = %2
  %9 = load i8*, i8** %4, align 4, !dbg !2379, !tbaa !432
  store i8* %9, i8** getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 2), align 4, !dbg !2381, !tbaa !2344
  br label %24, !dbg !2382

10:                                               ; preds = %2
  %11 = load i32, i32* %3, align 4, !dbg !2383, !tbaa !359
  %12 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 3), align 4, !dbg !2385, !tbaa !2228
  %13 = icmp eq i32 %11, %12, !dbg !2386
  br i1 %13, label %14, label %16, !dbg !2387

14:                                               ; preds = %10
  %15 = load i8*, i8** %4, align 4, !dbg !2388, !tbaa !432
  store i8* %15, i8** getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 5), align 4, !dbg !2390, !tbaa !2353
  br label %23, !dbg !2391

16:                                               ; preds = %10
  %17 = load i32, i32* %3, align 4, !dbg !2392, !tbaa !359
  %18 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 6), align 4, !dbg !2394, !tbaa !2235
  %19 = icmp eq i32 %17, %18, !dbg !2395
  br i1 %19, label %20, label %22, !dbg !2396

20:                                               ; preds = %16
  %21 = load i8*, i8** %4, align 4, !dbg !2397, !tbaa !432
  store i8* %21, i8** getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 8), align 4, !dbg !2399, !tbaa !2362
  br label %22, !dbg !2400

22:                                               ; preds = %20, %16
  br label %23

23:                                               ; preds = %22, %14
  br label %24

24:                                               ; preds = %23, %8
  ret void, !dbg !2401
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @get_secure_port_handle() #0 !dbg !2402 {
  %1 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 0), align 4, !dbg !2405, !tbaa !2220
  ret i32 %1, !dbg !2406
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @get_non_secure_port_handle() #0 !dbg !2407 {
  %1 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 3), align 4, !dbg !2408, !tbaa !2228
  ret i32 %1, !dbg !2409
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc i32 @get_current_chan_handle() #0 !dbg !2410 {
  %1 = load i32, i32* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 6), align 4, !dbg !2411, !tbaa !2235
  ret i32 %1, !dbg !2412
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc zeroext i1 @is_secure_port_active() #0 !dbg !2413 {
  %1 = load i8, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 1), align 4, !dbg !2414, !tbaa !2225, !range !2311
  %2 = trunc i8 %1 to i1, !dbg !2414
  ret i1 %2, !dbg !2415
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc zeroext i1 @is_non_secure_port_active() #0 !dbg !2416 {
  %1 = load i8, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 4), align 4, !dbg !2417, !tbaa !2232, !range !2311
  %2 = trunc i8 %1 to i1, !dbg !2417
  ret i1 %2, !dbg !2418
}

; Function Attrs: nounwind sspstrong
define dso_local arm_aapcscc zeroext i1 @is_current_chan_active() #0 !dbg !2419 {
  %1 = load i8, i8* getelementptr inbounds (%struct.handle_table, %struct.handle_table* @ht, i32 0, i32 7), align 4, !dbg !2420, !tbaa !2239, !range !2311
  %2 = trunc i8 %1 to i1, !dbg !2420
  ret i1 %2, !dbg !2421
}

attributes #0 = { nounwind sspstrong "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+aes,+armv8-a,+crc,+crypto,+d32,+dsp,+fp-armv8,+fp-armv8d16,+fp-armv8d16sp,+fp-armv8sp,+fp16,+fp64,+hwdiv,+hwdiv-arm,+neon,+sha2,+thumb-mode,+vfp2,+vfp2sp,+vfp3,+vfp3d16,+vfp3d16sp,+vfp3sp,+vfp4,+vfp4d16,+vfp4d16sp,+vfp4sp,-fp16fml,-fullfp16" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { argmemonly nounwind willreturn }
attributes #2 = { nounwind readnone speculatable willreturn }
attributes #3 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+aes,+armv8-a,+crc,+crypto,+d32,+dsp,+fp-armv8,+fp-armv8d16,+fp-armv8d16sp,+fp-armv8sp,+fp16,+fp64,+hwdiv,+hwdiv-arm,+neon,+sha2,+thumb-mode,+vfp2,+vfp2sp,+vfp3,+vfp3d16,+vfp3d16sp,+vfp3sp,+vfp4,+vfp4d16,+vfp4d16sp,+vfp4sp,-fp16fml,-fullfp16" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { inlinehint nounwind sspstrong "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+aes,+armv8-a,+crc,+crypto,+d32,+dsp,+fp-armv8,+fp-armv8d16,+fp-armv8d16sp,+fp-armv8sp,+fp16,+fp64,+hwdiv,+hwdiv-arm,+neon,+sha2,+thumb-mode,+vfp2,+vfp2sp,+vfp3,+vfp3d16,+vfp3d16sp,+vfp3sp,+vfp4,+vfp4d16,+vfp4d16sp,+vfp4sp,-fp16fml,-fullfp16" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noreturn "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="generic" "target-features"="+aes,+armv8-a,+crc,+crypto,+d32,+dsp,+fp-armv8,+fp-armv8d16,+fp-armv8d16sp,+fp-armv8sp,+fp16,+fp64,+hwdiv,+hwdiv-arm,+neon,+sha2,+thumb-mode,+vfp2,+vfp2sp,+vfp3,+vfp3d16,+vfp3d16sp,+vfp3sp,+vfp4,+vfp4d16,+vfp4d16sp,+vfp4sp,-fp16fml,-fullfp16" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #6 = { nounwind }
attributes #7 = { noreturn }

!llvm.dbg.cu = !{!238, !2, !157, !338, !221}
!llvm.ident = !{!341, !341, !341, !341, !341}
!llvm.module.flags = !{!342, !343, !344, !345}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "msg_buf", scope: !2, file: !154, line: 31, type: !31, isLocal: true, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C99, file: !3, producer: "Ubuntu clang version 10.0.1-++20200708123507+ef32c611aa2-1~exp1~20200707224105.191 ", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !4, retainedTypes: !15, globals: !151, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "/home/s2priya/seahorn/verify-trusty/verifyTrusty/seahorn/jobs/storage_ipc_msg_buffer/ipc.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!4 = !{!5}
!5 = !DICompositeType(tag: DW_TAG_enumeration_type, file: !6, line: 90, baseType: !7, size: 32, elements: !8)
!6 = !DIFile(filename: "trusty/user/base/include/user/trusty_ipc.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!7 = !DIBasicType(name: "unsigned int", size: 32, encoding: DW_ATE_unsigned)
!8 = !{!9, !10, !11, !12, !13, !14}
!9 = !DIEnumerator(name: "IPC_HANDLE_POLL_NONE", value: 0, isUnsigned: true)
!10 = !DIEnumerator(name: "IPC_HANDLE_POLL_READY", value: 1, isUnsigned: true)
!11 = !DIEnumerator(name: "IPC_HANDLE_POLL_ERROR", value: 2, isUnsigned: true)
!12 = !DIEnumerator(name: "IPC_HANDLE_POLL_HUP", value: 4, isUnsigned: true)
!13 = !DIEnumerator(name: "IPC_HANDLE_POLL_MSG", value: 8, isUnsigned: true)
!14 = !DIEnumerator(name: "IPC_HANDLE_POLL_SEND_UNBLOCKED", value: 16, isUnsigned: true)
!15 = !{!16, !31, !40, !33, !43, !37, !49, !52, !55, !96, !97, !98, !102, !105, !114, !117, !147}
!16 = !DISubprogram(name: "send_msg", scope: !6, file: !6, line: 139, type: !17, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!17 = !DISubroutineType(types: !18)
!18 = !{!19, !19, !20}
!19 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!20 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !21, size: 32)
!21 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_msg", file: !6, line: 72, size: 128, elements: !22)
!22 = !{!23, !26, !34, !35}
!23 = !DIDerivedType(tag: DW_TAG_member, name: "num_iov", scope: !21, file: !6, line: 73, baseType: !24, size: 32)
!24 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint32_t", file: !25, line: 159, baseType: !7)
!25 = !DIFile(filename: "external/trusty/musl/arch/arm/bits/alltypes.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!26 = !DIDerivedType(tag: DW_TAG_member, name: "iov", scope: !21, file: !6, line: 74, baseType: !27, size: 32, offset: 32)
!27 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !28, size: 32)
!28 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "iovec", file: !25, line: 372, size: 64, elements: !29)
!29 = !{!30, !32}
!30 = !DIDerivedType(tag: DW_TAG_member, name: "iov_base", scope: !28, file: !25, line: 372, baseType: !31, size: 32)
!31 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 32)
!32 = !DIDerivedType(tag: DW_TAG_member, name: "iov_len", scope: !28, file: !25, line: 372, baseType: !33, size: 32, offset: 32)
!33 = !DIDerivedType(tag: DW_TAG_typedef, name: "size_t", file: !25, line: 88, baseType: !7)
!34 = !DIDerivedType(tag: DW_TAG_member, name: "num_handles", scope: !21, file: !6, line: 76, baseType: !24, size: 32, offset: 64)
!35 = !DIDerivedType(tag: DW_TAG_member, name: "handles", scope: !21, file: !6, line: 77, baseType: !36, size: 32, offset: 96)
!36 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !37, size: 32)
!37 = !DIDerivedType(tag: DW_TAG_typedef, name: "handle_t", file: !6, line: 38, baseType: !38)
!38 = !DIDerivedType(tag: DW_TAG_typedef, name: "int32_t", file: !25, line: 134, baseType: !19)
!39 = !{}
!40 = !DISubprogram(name: "put_msg", scope: !6, file: !6, line: 138, type: !41, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!41 = !DISubroutineType(types: !42)
!42 = !{!19, !19, !7}
!43 = !DISubprogram(name: "port_create", scope: !6, file: !6, line: 121, type: !44, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!44 = !DISubroutineType(types: !45)
!45 = !{!19, !46, !7, !7, !7}
!46 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !47, size: 32)
!47 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !48)
!48 = !DIBasicType(name: "char", size: 8, encoding: DW_ATE_unsigned_char)
!49 = !DISubprogram(name: "set_cookie", scope: !6, file: !6, line: 128, type: !50, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!50 = !DISubroutineType(types: !51)
!51 = !{!19, !19, !31}
!52 = !DISubprogram(name: "close", scope: !6, file: !6, line: 127, type: !53, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!53 = !DISubroutineType(types: !54)
!54 = !{!19, !19}
!55 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !56, size: 32)
!56 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_channel_context", file: !57, line: 90, size: 192, elements: !58)
!57 = !DIFile(filename: "trusty/user/app/storage/ipc.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!58 = !{!59, !76, !89}
!59 = !DIDerivedType(tag: DW_TAG_member, name: "common", scope: !56, file: !57, line: 91, baseType: !60, size: 64)
!60 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_context", file: !57, line: 85, size: 64, elements: !61)
!61 = !{!62, !75}
!62 = !DIDerivedType(tag: DW_TAG_member, name: "evt_handler", scope: !60, file: !57, line: 86, baseType: !63, size: 32)
!63 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_evt_handler_t", file: !57, line: 64, baseType: !64)
!64 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !65, size: 32)
!65 = !DISubroutineType(types: !66)
!66 = !{null, !67, !68}
!67 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !60, size: 32)
!68 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !69, size: 32)
!69 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !70)
!70 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "uevent", file: !6, line: 112, size: 96, elements: !71)
!71 = !{!72, !73, !74}
!72 = !DIDerivedType(tag: DW_TAG_member, name: "handle", scope: !70, file: !6, line: 113, baseType: !37, size: 32)
!73 = !DIDerivedType(tag: DW_TAG_member, name: "event", scope: !70, file: !6, line: 114, baseType: !24, size: 32, offset: 32)
!74 = !DIDerivedType(tag: DW_TAG_member, name: "cookie", scope: !70, file: !6, line: 115, baseType: !31, size: 32, offset: 64)
!75 = !DIDerivedType(tag: DW_TAG_member, name: "handle", scope: !60, file: !57, line: 87, baseType: !37, size: 32, offset: 32)
!76 = !DIDerivedType(tag: DW_TAG_member, name: "ops", scope: !56, file: !57, line: 92, baseType: !77, size: 64, offset: 64)
!77 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_channel_ops", file: !57, line: 80, size: 64, elements: !78)
!78 = !{!79, !84}
!79 = !DIDerivedType(tag: DW_TAG_member, name: "on_handle_msg", scope: !77, file: !57, line: 81, baseType: !80, size: 32)
!80 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_msg_handler_t", file: !57, line: 52, baseType: !81)
!81 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !82, size: 32)
!82 = !DISubroutineType(types: !83)
!83 = !{!19, !55, !31, !33}
!84 = !DIDerivedType(tag: DW_TAG_member, name: "on_disconnect", scope: !77, file: !57, line: 82, baseType: !85, size: 32, offset: 32)
!85 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_disconnect_handler_t", file: !57, line: 62, baseType: !86)
!86 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !87, size: 32)
!87 = !DISubroutineType(types: !88)
!88 = !{null, !55}
!89 = !DIDerivedType(tag: DW_TAG_member, name: "node", scope: !56, file: !57, line: 93, baseType: !90, size: 64, offset: 128)
!90 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "list_node", file: !91, line: 34, size: 64, elements: !92)
!91 = !DIFile(filename: "external/lk/include/shared/lk/list.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!92 = !{!93, !95}
!93 = !DIDerivedType(tag: DW_TAG_member, name: "prev", scope: !90, file: !91, line: 35, baseType: !94, size: 32)
!94 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !90, size: 32)
!95 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !90, file: !91, line: 36, baseType: !94, size: 32, offset: 32)
!96 = !DIDerivedType(tag: DW_TAG_typedef, name: "uintptr_t", file: !25, line: 93, baseType: !7)
!97 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !48, size: 32)
!98 = !DISubprogram(name: "wait_any", scope: !6, file: !6, line: 132, type: !99, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!99 = !DISubroutineType(types: !100)
!100 = !{!19, !101, !7}
!101 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !70, size: 32)
!102 = !DISubprogram(name: "wait", scope: !6, file: !6, line: 131, type: !103, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!103 = !DISubroutineType(types: !104)
!104 = !{!19, !19, !101, !7}
!105 = !DISubprogram(name: "get_msg", scope: !6, file: !6, line: 133, type: !106, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!106 = !DISubroutineType(types: !107)
!107 = !{!19, !19, !108}
!108 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !109, size: 32)
!109 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_msg_info", file: !6, line: 80, size: 96, elements: !110)
!110 = !{!111, !112, !113}
!111 = !DIDerivedType(tag: DW_TAG_member, name: "len", scope: !109, file: !6, line: 81, baseType: !33, size: 32)
!112 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !109, file: !6, line: 82, baseType: !24, size: 32, offset: 32)
!113 = !DIDerivedType(tag: DW_TAG_member, name: "num_handles", scope: !109, file: !6, line: 83, baseType: !24, size: 32, offset: 64)
!114 = !DISubprogram(name: "read_msg", scope: !6, file: !6, line: 134, type: !115, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!115 = !DISubroutineType(types: !116)
!116 = !{!19, !19, !7, !7, !20}
!117 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !118, size: 32)
!118 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_port_context", file: !57, line: 96, size: 160, elements: !119)
!119 = !{!120, !121, !146}
!120 = !DIDerivedType(tag: DW_TAG_member, name: "common", scope: !118, file: !57, line: 97, baseType: !60, size: 64)
!121 = !DIDerivedType(tag: DW_TAG_member, name: "ops", scope: !118, file: !57, line: 98, baseType: !122, size: 32, offset: 64)
!122 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_port_ops", file: !57, line: 71, size: 32, elements: !123)
!123 = !{!124}
!124 = !DIDerivedType(tag: DW_TAG_member, name: "on_connect", scope: !122, file: !57, line: 72, baseType: !125, size: 32)
!125 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_connect_handler_t", file: !57, line: 38, baseType: !126)
!126 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !127, size: 32)
!127 = !DISubroutineType(types: !128)
!128 = !{!55, !117, !129, !37}
!129 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !130, size: 32)
!130 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !131)
!131 = !DIDerivedType(tag: DW_TAG_typedef, name: "uuid_t", file: !132, line: 33, baseType: !133)
!132 = !DIFile(filename: "trusty/kernel/include/uapi/uapi/trusty_uuid.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!133 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "uuid", file: !132, line: 28, size: 128, elements: !134)
!134 = !{!135, !136, !139, !140}
!135 = !DIDerivedType(tag: DW_TAG_member, name: "time_low", scope: !133, file: !132, line: 29, baseType: !24, size: 32)
!136 = !DIDerivedType(tag: DW_TAG_member, name: "time_mid", scope: !133, file: !132, line: 30, baseType: !137, size: 16, offset: 32)
!137 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint16_t", file: !25, line: 154, baseType: !138)
!138 = !DIBasicType(name: "unsigned short", size: 16, encoding: DW_ATE_unsigned)
!139 = !DIDerivedType(tag: DW_TAG_member, name: "time_hi_and_version", scope: !133, file: !132, line: 31, baseType: !137, size: 16, offset: 48)
!140 = !DIDerivedType(tag: DW_TAG_member, name: "clock_seq_and_node", scope: !133, file: !132, line: 32, baseType: !141, size: 64, offset: 64)
!141 = !DICompositeType(tag: DW_TAG_array_type, baseType: !142, size: 64, elements: !144)
!142 = !DIDerivedType(tag: DW_TAG_typedef, name: "uint8_t", file: !25, line: 149, baseType: !143)
!143 = !DIBasicType(name: "unsigned char", size: 8, encoding: DW_ATE_unsigned_char)
!144 = !{!145}
!145 = !DISubrange(count: 8)
!146 = !DIDerivedType(tag: DW_TAG_member, name: "channels", scope: !118, file: !57, line: 99, baseType: !90, size: 64, offset: 96)
!147 = !DISubprogram(name: "accept", scope: !6, file: !6, line: 126, type: !148, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!148 = !DISubroutineType(types: !149)
!149 = !{!19, !19, !150}
!150 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !133, size: 32)
!151 = !{!152, !0}
!152 = !DIGlobalVariableExpression(var: !153, expr: !DIExpression())
!153 = distinct !DIGlobalVariable(name: "msg_buf_size", scope: !2, file: !154, line: 32, type: !33, isLocal: true, isDefinition: true)
!154 = !DIFile(filename: "seahorn/jobs/storage_ipc_msg_buffer/ipc.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!155 = !DIGlobalVariableExpression(var: !156, expr: !DIExpression())
!156 = distinct !DIGlobalVariable(name: "cur_msg_id", scope: !157, file: !166, line: 21, type: !24, isLocal: true, isDefinition: true)
!157 = distinct !DICompileUnit(language: DW_LANG_C99, file: !158, producer: "Ubuntu clang version 10.0.1-++20200708123507+ef32c611aa2-1~exp1~20200707224105.191 ", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !159, retainedTypes: !164, globals: !216, splitDebugInlining: false, nameTableKind: None)
!158 = !DIFile(filename: "/home/s2priya/seahorn/verify-trusty/verifyTrusty/seahorn/stubs/wide/trusty_msg.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!159 = !{!160}
!160 = !DICompositeType(tag: DW_TAG_enumeration_type, file: !6, line: 54, baseType: !7, size: 32, elements: !161)
!161 = !{!162, !163}
!162 = !DIEnumerator(name: "IPC_PORT_ALLOW_TA_CONNECT", value: 1, isUnsigned: true)
!163 = !DIEnumerator(name: "IPC_PORT_ALLOW_NS_CONNECT", value: 2, isUnsigned: true)
!164 = !{!165, !169, !172, !173, !174, !179, !180, !181, !182, !186, !24, !187, !190, !191, !192, !193, !194, !195, !196, !197, !198, !201, !204, !205, !208, !209, !210, !213, !214, !215}
!165 = !DISubprogram(name: "nd_get_msg_ret", scope: !166, file: !166, line: 31, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!166 = !DIFile(filename: "seahorn/stubs/wide/trusty_msg.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!167 = !DISubroutineType(types: !168)
!168 = !{!19}
!169 = !DISubprogram(name: "nd_msg_len", scope: !166, file: !166, line: 29, type: !170, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!170 = !DISubroutineType(types: !171)
!171 = !{!7}
!172 = !DISubprogram(name: "nd_msg_id", scope: !166, file: !166, line: 30, type: !170, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!173 = !DISubprogram(name: "nd_read_msg_ret", scope: !166, file: !166, line: 56, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!174 = !DISubprogram(name: "sea_is_dereferenceable", scope: !175, file: !175, line: 28, type: !176, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!175 = !DIFile(filename: "priyasiddharth-seahorn/seahorn/build-dbg/run/include/seahorn/seahorn.h", directory: "/home/s2priya/seahorn")
!176 = !DISubroutineType(types: !177)
!177 = !{!178, !31, !19}
!178 = !DIBasicType(name: "_Bool", size: 8, encoding: DW_ATE_boolean)
!179 = !DISubprogram(name: "nd_send_msg_ret", scope: !166, file: !166, line: 82, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!180 = !DISubprogram(name: "nd_put_msg_ret", scope: !166, file: !166, line: 101, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!181 = !DISubprogram(name: "nd_wait_ret", scope: !166, file: !166, line: 112, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!182 = !DISubprogram(name: "get_handle_cookie", scope: !183, file: !183, line: 36, type: !184, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!183 = !DIFile(filename: "seahorn/include/handle_table.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!184 = !DISubroutineType(types: !185)
!185 = !{!31, !19}
!186 = !DISubprogram(name: "nd_event_flag", scope: !166, file: !166, line: 113, type: !170, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!187 = !DISubprogram(name: "is_current_chan_active", scope: !183, file: !183, line: 46, type: !188, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!188 = !DISubroutineType(types: !189)
!189 = !{!178}
!190 = !DISubprogram(name: "get_current_chan_handle", scope: !183, file: !183, line: 42, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!191 = !DISubprogram(name: "is_secure_port_active", scope: !183, file: !183, line: 44, type: !188, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!192 = !DISubprogram(name: "get_secure_port_handle", scope: !183, file: !183, line: 40, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!193 = !DISubprogram(name: "is_non_secure_port_active", scope: !183, file: !183, line: 45, type: !188, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!194 = !DISubprogram(name: "get_non_secure_port_handle", scope: !183, file: !183, line: 41, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!195 = !DISubprogram(name: "nd_wait_handle", scope: !166, file: !166, line: 128, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!196 = !DISubprogram(name: "nd_wait_any_ret", scope: !166, file: !166, line: 129, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!197 = !DISubprogram(name: "nd_port_handle", scope: !166, file: !166, line: 164, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!198 = !DISubprogram(name: "add_handle", scope: !183, file: !183, line: 33, type: !199, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!199 = !DISubroutineType(types: !200)
!200 = !{null, !19}
!201 = !DISubprogram(name: "contains_handle", scope: !183, file: !183, line: 35, type: !202, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!202 = !DISubroutineType(types: !203)
!203 = !{!178, !19}
!204 = !DISubprogram(name: "nd_set_cookie_ret", scope: !166, file: !166, line: 191, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!205 = !DISubprogram(name: "set_handle_cookie", scope: !183, file: !183, line: 37, type: !206, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!206 = !DISubroutineType(types: !207)
!207 = !{null, !19, !31}
!208 = !DISubprogram(name: "nd_chan_handle", scope: !166, file: !166, line: 206, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!209 = !DISubprogram(name: "nd_time_low", scope: !166, file: !166, line: 207, type: !170, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!210 = !DISubprogram(name: "nd_time_mid", scope: !166, file: !166, line: 208, type: !211, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!211 = !DISubroutineType(types: !212)
!212 = !{!138}
!213 = !DISubprogram(name: "nd_time_hi_n_ver", scope: !166, file: !166, line: 209, type: !211, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!214 = !DISubprogram(name: "nd_close_ret", scope: !166, file: !166, line: 226, type: !167, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!215 = !DISubprogram(name: "remove_handle", scope: !183, file: !183, line: 34, type: !199, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!216 = !{!155, !217}
!217 = !DIGlobalVariableExpression(var: !218, expr: !DIExpression())
!218 = distinct !DIGlobalVariable(name: "cur_msg_retired", scope: !157, file: !166, line: 22, type: !178, isLocal: true, isDefinition: true)
!219 = !DIGlobalVariableExpression(var: !220, expr: !DIExpression())
!220 = distinct !DIGlobalVariable(name: "ht", scope: !221, file: !225, line: 13, type: !226, isLocal: true, isDefinition: true)
!221 = distinct !DICompileUnit(language: DW_LANG_C99, file: !222, producer: "Ubuntu clang version 10.0.1-++20200708123507+ef32c611aa2-1~exp1~20200707224105.191 ", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !39, retainedTypes: !223, globals: !224, splitDebugInlining: false, nameTableKind: None)
!222 = !DIFile(filename: "/home/s2priya/seahorn/verify-trusty/verifyTrusty/seahorn/lib/handle_table.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!223 = !{!37, !31}
!224 = !{!219}
!225 = !DIFile(filename: "seahorn/lib/handle_table.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!226 = !DIDerivedType(tag: DW_TAG_typedef, name: "handle_table_t", file: !183, line: 29, baseType: !227)
!227 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "handle_table", file: !183, line: 14, size: 288, elements: !228)
!228 = !{!229, !230, !231, !232, !233, !234, !235, !236, !237}
!229 = !DIDerivedType(tag: DW_TAG_member, name: "secure_port_handle", scope: !227, file: !183, line: 18, baseType: !37, size: 32)
!230 = !DIDerivedType(tag: DW_TAG_member, name: "secure_port_handle_active", scope: !227, file: !183, line: 19, baseType: !178, size: 8, offset: 32)
!231 = !DIDerivedType(tag: DW_TAG_member, name: "secure_port_cookie", scope: !227, file: !183, line: 20, baseType: !31, size: 32, offset: 64)
!232 = !DIDerivedType(tag: DW_TAG_member, name: "non_secure_port_handle", scope: !227, file: !183, line: 22, baseType: !37, size: 32, offset: 96)
!233 = !DIDerivedType(tag: DW_TAG_member, name: "non_secure_port_handle_active", scope: !227, file: !183, line: 23, baseType: !178, size: 8, offset: 128)
!234 = !DIDerivedType(tag: DW_TAG_member, name: "non_secure_port_cookie", scope: !227, file: !183, line: 24, baseType: !31, size: 32, offset: 160)
!235 = !DIDerivedType(tag: DW_TAG_member, name: "chan_handle", scope: !227, file: !183, line: 26, baseType: !37, size: 32, offset: 192)
!236 = !DIDerivedType(tag: DW_TAG_member, name: "chan_handle_active", scope: !227, file: !183, line: 27, baseType: !178, size: 8, offset: 224)
!237 = !DIDerivedType(tag: DW_TAG_member, name: "chan_cookie", scope: !227, file: !183, line: 28, baseType: !31, size: 32, offset: 256)
!238 = distinct !DICompileUnit(language: DW_LANG_C99, file: !239, producer: "Ubuntu clang version 10.0.1-++20200708123507+ef32c611aa2-1~exp1~20200707224105.191 ", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !159, retainedTypes: !240, splitDebugInlining: false, nameTableKind: None)
!239 = !DIFile(filename: "/home/s2priya/seahorn/verify-trusty/verifyTrusty/seahorn/jobs/storage_ipc_msg_buffer/main.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!240 = !{!37, !241, !244, !31, !308, !312, !316, !319, !323}
!241 = !DISubprogram(name: "handle_table_init", scope: !183, file: !183, line: 32, type: !242, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!242 = !DISubroutineType(types: !243)
!243 = !{null, !19, !19, !19}
!244 = !DISubprogram(name: "ipc_port_create", scope: !57, file: !57, line: 116, type: !245, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!245 = !DISubroutineType(types: !246)
!246 = !{!19, !247, !46, !7, !7, !7}
!247 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !248, size: 32)
!248 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_port_context", file: !57, line: 96, size: 160, elements: !249)
!249 = !{!250, !267, !307}
!250 = !DIDerivedType(tag: DW_TAG_member, name: "common", scope: !248, file: !57, line: 97, baseType: !251, size: 64)
!251 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_context", file: !57, line: 85, size: 64, elements: !252)
!252 = !{!253, !266}
!253 = !DIDerivedType(tag: DW_TAG_member, name: "evt_handler", scope: !251, file: !57, line: 86, baseType: !254, size: 32)
!254 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_evt_handler_t", file: !57, line: 64, baseType: !255)
!255 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !256, size: 32)
!256 = !DISubroutineType(types: !257)
!257 = !{null, !258, !259}
!258 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !251, size: 32)
!259 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !260, size: 32)
!260 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !261)
!261 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "uevent", file: !6, line: 112, size: 96, elements: !262)
!262 = !{!263, !264, !265}
!263 = !DIDerivedType(tag: DW_TAG_member, name: "handle", scope: !261, file: !6, line: 113, baseType: !37, size: 32)
!264 = !DIDerivedType(tag: DW_TAG_member, name: "event", scope: !261, file: !6, line: 114, baseType: !24, size: 32, offset: 32)
!265 = !DIDerivedType(tag: DW_TAG_member, name: "cookie", scope: !261, file: !6, line: 115, baseType: !31, size: 32, offset: 64)
!266 = !DIDerivedType(tag: DW_TAG_member, name: "handle", scope: !251, file: !57, line: 87, baseType: !37, size: 32, offset: 32)
!267 = !DIDerivedType(tag: DW_TAG_member, name: "ops", scope: !248, file: !57, line: 98, baseType: !268, size: 32, offset: 64)
!268 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_port_ops", file: !57, line: 71, size: 32, elements: !269)
!269 = !{!270}
!270 = !DIDerivedType(tag: DW_TAG_member, name: "on_connect", scope: !268, file: !57, line: 72, baseType: !271, size: 32)
!271 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_connect_handler_t", file: !57, line: 38, baseType: !272)
!272 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !273, size: 32)
!273 = !DISubroutineType(types: !274)
!274 = !{!275, !247, !298, !37}
!275 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !276, size: 32)
!276 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_channel_context", file: !57, line: 90, size: 192, elements: !277)
!277 = !{!278, !279, !292}
!278 = !DIDerivedType(tag: DW_TAG_member, name: "common", scope: !276, file: !57, line: 91, baseType: !251, size: 64)
!279 = !DIDerivedType(tag: DW_TAG_member, name: "ops", scope: !276, file: !57, line: 92, baseType: !280, size: 64, offset: 64)
!280 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_channel_ops", file: !57, line: 80, size: 64, elements: !281)
!281 = !{!282, !287}
!282 = !DIDerivedType(tag: DW_TAG_member, name: "on_handle_msg", scope: !280, file: !57, line: 81, baseType: !283, size: 32)
!283 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_msg_handler_t", file: !57, line: 52, baseType: !284)
!284 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !285, size: 32)
!285 = !DISubroutineType(types: !286)
!286 = !{!19, !275, !31, !33}
!287 = !DIDerivedType(tag: DW_TAG_member, name: "on_disconnect", scope: !280, file: !57, line: 82, baseType: !288, size: 32, offset: 32)
!288 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_disconnect_handler_t", file: !57, line: 62, baseType: !289)
!289 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !290, size: 32)
!290 = !DISubroutineType(types: !291)
!291 = !{null, !275}
!292 = !DIDerivedType(tag: DW_TAG_member, name: "node", scope: !276, file: !57, line: 93, baseType: !293, size: 64, offset: 128)
!293 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "list_node", file: !91, line: 34, size: 64, elements: !294)
!294 = !{!295, !297}
!295 = !DIDerivedType(tag: DW_TAG_member, name: "prev", scope: !293, file: !91, line: 35, baseType: !296, size: 32)
!296 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !293, size: 32)
!297 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !293, file: !91, line: 36, baseType: !296, size: 32, offset: 32)
!298 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !299, size: 32)
!299 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !300)
!300 = !DIDerivedType(tag: DW_TAG_typedef, name: "uuid_t", file: !132, line: 33, baseType: !301)
!301 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "uuid", file: !132, line: 28, size: 128, elements: !302)
!302 = !{!303, !304, !305, !306}
!303 = !DIDerivedType(tag: DW_TAG_member, name: "time_low", scope: !301, file: !132, line: 29, baseType: !24, size: 32)
!304 = !DIDerivedType(tag: DW_TAG_member, name: "time_mid", scope: !301, file: !132, line: 30, baseType: !137, size: 16, offset: 32)
!305 = !DIDerivedType(tag: DW_TAG_member, name: "time_hi_and_version", scope: !301, file: !132, line: 31, baseType: !137, size: 16, offset: 48)
!306 = !DIDerivedType(tag: DW_TAG_member, name: "clock_seq_and_node", scope: !301, file: !132, line: 32, baseType: !141, size: 64, offset: 64)
!307 = !DIDerivedType(tag: DW_TAG_member, name: "channels", scope: !248, file: !57, line: 99, baseType: !293, size: 64, offset: 96)
!308 = !DISubprogram(name: "wait_any", scope: !6, file: !6, line: 132, type: !309, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!309 = !DISubroutineType(types: !310)
!310 = !{!19, !311, !7}
!311 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !261, size: 32)
!312 = !DISubprogram(name: "dispatch_event", scope: !313, file: !313, line: 17, type: !314, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!313 = !DIFile(filename: "seahorn/jobs/storage_ipc_msg_buffer/main.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!314 = !DISubroutineType(types: !315)
!315 = !{null, !259}
!316 = !DISubprogram(name: "ipc_port_destroy", scope: !57, file: !57, line: 121, type: !317, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!317 = !DISubroutineType(types: !318)
!318 = !{!19, !247}
!319 = !DISubprogram(name: "free", scope: !320, file: !320, line: 41, type: !321, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!320 = !DIFile(filename: "external/trusty/musl/include/stdlib.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!321 = !DISubroutineType(types: !322)
!322 = !{null, !31}
!323 = !DISubprogram(name: "send_msg", scope: !6, file: !6, line: 139, type: !324, flags: DIFlagPrototyped, spFlags: DISPFlagOptimized, retainedNodes: !39)
!324 = !DISubroutineType(types: !325)
!325 = !{!19, !19, !326}
!326 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !327, size: 32)
!327 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_msg", file: !6, line: 72, size: 128, elements: !328)
!328 = !{!329, !330, !336, !337}
!329 = !DIDerivedType(tag: DW_TAG_member, name: "num_iov", scope: !327, file: !6, line: 73, baseType: !24, size: 32)
!330 = !DIDerivedType(tag: DW_TAG_member, name: "iov", scope: !327, file: !6, line: 74, baseType: !331, size: 32, offset: 32)
!331 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !332, size: 32)
!332 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "iovec", file: !25, line: 372, size: 64, elements: !333)
!333 = !{!334, !335}
!334 = !DIDerivedType(tag: DW_TAG_member, name: "iov_base", scope: !332, file: !25, line: 372, baseType: !31, size: 32)
!335 = !DIDerivedType(tag: DW_TAG_member, name: "iov_len", scope: !332, file: !25, line: 372, baseType: !33, size: 32, offset: 32)
!336 = !DIDerivedType(tag: DW_TAG_member, name: "num_handles", scope: !327, file: !6, line: 76, baseType: !24, size: 32, offset: 64)
!337 = !DIDerivedType(tag: DW_TAG_member, name: "handles", scope: !327, file: !6, line: 77, baseType: !36, size: 32, offset: 96)
!338 = distinct !DICompileUnit(language: DW_LANG_C99, file: !339, producer: "Ubuntu clang version 10.0.1-++20200708123507+ef32c611aa2-1~exp1~20200707224105.191 ", isOptimized: true, runtimeVersion: 0, emissionKind: FullDebug, enums: !39, retainedTypes: !340, splitDebugInlining: false, nameTableKind: None)
!339 = !DIFile(filename: "/home/s2priya/seahorn/verify-trusty/verifyTrusty/seahorn/stubs/realloc.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!340 = !{!319}
!341 = !{!"Ubuntu clang version 10.0.1-++20200708123507+ef32c611aa2-1~exp1~20200707224105.191 "}
!342 = !{i32 7, !"Dwarf Version", i32 4}
!343 = !{i32 2, !"Debug Info Version", i32 3}
!344 = !{i32 1, !"wchar_size", i32 4}
!345 = !{i32 1, !"min_enum_size", i32 4}
!346 = distinct !DISubprogram(name: "main", scope: !313, file: !313, line: 57, type: !167, scopeLine: 57, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !238, retainedNodes: !347)
!347 = !{!348, !349, !350, !352}
!348 = !DILocalVariable(name: "ctx", scope: !346, file: !313, line: 59, type: !248)
!349 = !DILocalVariable(name: "rc", scope: !346, file: !313, line: 62, type: !19)
!350 = !DILocalVariable(name: "event1", scope: !346, file: !313, line: 72, type: !351)
!351 = !DIDerivedType(tag: DW_TAG_typedef, name: "uevent_t", file: !6, line: 116, baseType: !261)
!352 = !DILocalVariable(name: "event2", scope: !346, file: !313, line: 84, type: !351)
!353 = !DILocation(line: 58, column: 3, scope: !346)
!354 = !DILocation(line: 59, column: 3, scope: !346)
!355 = !DILocation(line: 59, column: 27, scope: !346)
!356 = !DILocation(line: 62, column: 3, scope: !346)
!357 = !DILocation(line: 62, column: 7, scope: !346)
!358 = !DILocation(line: 63, column: 7, scope: !346)
!359 = !{!360, !360, i64 0}
!360 = !{!"int", !361, i64 0}
!361 = !{!"omnipotent char", !362, i64 0}
!362 = !{!"Simple C/C++ TBAA"}
!363 = !DILocation(line: 66, column: 7, scope: !364)
!364 = distinct !DILexicalBlock(scope: !346, file: !313, line: 66, column: 7)
!365 = !DILocation(line: 66, column: 10, scope: !364)
!366 = !DILocation(line: 66, column: 7, scope: !346)
!367 = !DILocation(line: 67, column: 12, scope: !368)
!368 = distinct !DILexicalBlock(scope: !364, file: !313, line: 66, column: 15)
!369 = !DILocation(line: 67, column: 5, scope: !368)
!370 = !DILocation(line: 72, column: 3, scope: !346)
!371 = !DILocation(line: 72, column: 12, scope: !346)
!372 = !DILocation(line: 73, column: 10, scope: !346)
!373 = !DILocation(line: 73, column: 17, scope: !346)
!374 = !{!375, !360, i64 0}
!375 = !{!"uevent", !360, i64 0, !360, i64 4, !376, i64 8}
!376 = !{!"any pointer", !361, i64 0}
!377 = !DILocation(line: 74, column: 10, scope: !346)
!378 = !DILocation(line: 74, column: 16, scope: !346)
!379 = !{!375, !360, i64 4}
!380 = !DILocation(line: 75, column: 10, scope: !346)
!381 = !DILocation(line: 75, column: 17, scope: !346)
!382 = !{!375, !376, i64 8}
!383 = !DILocation(line: 76, column: 8, scope: !346)
!384 = !DILocation(line: 76, column: 6, scope: !346)
!385 = !DILocation(line: 77, column: 7, scope: !386)
!386 = distinct !DILexicalBlock(scope: !346, file: !313, line: 77, column: 7)
!387 = !DILocation(line: 77, column: 10, scope: !386)
!388 = !DILocation(line: 77, column: 7, scope: !346)
!389 = !DILocation(line: 78, column: 12, scope: !390)
!390 = distinct !DILexicalBlock(scope: !386, file: !313, line: 77, column: 15)
!391 = !DILocation(line: 78, column: 5, scope: !390)
!392 = !DILocation(line: 80, column: 7, scope: !393)
!393 = distinct !DILexicalBlock(scope: !346, file: !313, line: 80, column: 7)
!394 = !DILocation(line: 80, column: 10, scope: !393)
!395 = !DILocation(line: 80, column: 7, scope: !346)
!396 = !DILocation(line: 81, column: 5, scope: !397)
!397 = distinct !DILexicalBlock(scope: !393, file: !313, line: 80, column: 23)
!398 = !DILocation(line: 82, column: 3, scope: !397)
!399 = !DILocation(line: 84, column: 3, scope: !346)
!400 = !DILocation(line: 84, column: 12, scope: !346)
!401 = !DILocation(line: 85, column: 10, scope: !346)
!402 = !DILocation(line: 85, column: 17, scope: !346)
!403 = !DILocation(line: 86, column: 10, scope: !346)
!404 = !DILocation(line: 86, column: 16, scope: !346)
!405 = !DILocation(line: 87, column: 10, scope: !346)
!406 = !DILocation(line: 87, column: 17, scope: !346)
!407 = !DILocation(line: 88, column: 8, scope: !346)
!408 = !DILocation(line: 88, column: 6, scope: !346)
!409 = !DILocation(line: 89, column: 7, scope: !410)
!410 = distinct !DILexicalBlock(scope: !346, file: !313, line: 89, column: 7)
!411 = !DILocation(line: 89, column: 10, scope: !410)
!412 = !DILocation(line: 89, column: 7, scope: !346)
!413 = !DILocation(line: 90, column: 12, scope: !414)
!414 = distinct !DILexicalBlock(scope: !410, file: !313, line: 89, column: 15)
!415 = !DILocation(line: 90, column: 5, scope: !414)
!416 = !DILocation(line: 92, column: 7, scope: !417)
!417 = distinct !DILexicalBlock(scope: !346, file: !313, line: 92, column: 7)
!418 = !DILocation(line: 92, column: 10, scope: !417)
!419 = !DILocation(line: 92, column: 7, scope: !346)
!420 = !DILocation(line: 93, column: 5, scope: !421)
!421 = distinct !DILexicalBlock(scope: !417, file: !313, line: 92, column: 23)
!422 = !DILocation(line: 94, column: 3, scope: !421)
!423 = !DILocation(line: 96, column: 3, scope: !346)
!424 = !DILocation(line: 98, column: 3, scope: !346)
!425 = !DILocation(line: 99, column: 1, scope: !346)
!426 = distinct !DISubprogram(name: "sea_channel_connect", scope: !313, file: !313, line: 46, type: !273, scopeLine: 47, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !238, retainedNodes: !427)
!427 = !{!428, !429, !430, !431}
!428 = !DILocalVariable(name: "parent_ctx", arg: 1, scope: !426, file: !313, line: 46, type: !247)
!429 = !DILocalVariable(name: "peer_uuid", arg: 2, scope: !426, file: !313, line: 47, type: !298)
!430 = !DILocalVariable(name: "chan_handle", arg: 3, scope: !426, file: !313, line: 47, type: !37)
!431 = !DILocalVariable(name: "pctx", scope: !426, file: !313, line: 48, type: !275)
!432 = !{!376, !376, i64 0}
!433 = !DILocation(line: 46, column: 46, scope: !426)
!434 = !DILocation(line: 47, column: 35, scope: !426)
!435 = !DILocation(line: 47, column: 55, scope: !426)
!436 = !DILocation(line: 48, column: 3, scope: !426)
!437 = !DILocation(line: 48, column: 31, scope: !426)
!438 = !DILocation(line: 48, column: 38, scope: !426)
!439 = !DILocation(line: 49, column: 3, scope: !426)
!440 = !DILocation(line: 49, column: 9, scope: !426)
!441 = !DILocation(line: 49, column: 13, scope: !426)
!442 = !DILocation(line: 49, column: 27, scope: !426)
!443 = !{!444, !376, i64 12}
!444 = !{!"ipc_channel_context", !445, i64 0, !446, i64 8, !447, i64 16}
!445 = !{!"ipc_context", !376, i64 0, !360, i64 4}
!446 = !{!"ipc_channel_ops", !376, i64 0, !376, i64 4}
!447 = !{!"list_node", !376, i64 0, !376, i64 4}
!448 = !DILocation(line: 50, column: 3, scope: !426)
!449 = !DILocation(line: 50, column: 9, scope: !426)
!450 = !DILocation(line: 50, column: 13, scope: !426)
!451 = !DILocation(line: 50, column: 27, scope: !426)
!452 = !{!444, !376, i64 8}
!453 = !DILocation(line: 51, column: 10, scope: !426)
!454 = !DILocation(line: 52, column: 1, scope: !426)
!455 = !DILocation(line: 51, column: 3, scope: !426)
!456 = distinct !DISubprogram(name: "sea_ipc_disconnect_handler", scope: !313, file: !313, line: 19, type: !290, scopeLine: 19, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !238, retainedNodes: !457)
!457 = !{!458}
!458 = !DILocalVariable(name: "context", arg: 1, scope: !456, file: !313, line: 19, type: !275)
!459 = !DILocation(line: 19, column: 68, scope: !456)
!460 = !DILocation(line: 20, column: 7, scope: !461)
!461 = distinct !DILexicalBlock(scope: !456, file: !313, line: 20, column: 7)
!462 = !DILocation(line: 20, column: 7, scope: !456)
!463 = !DILocation(line: 21, column: 10, scope: !461)
!464 = !DILocation(line: 21, column: 5, scope: !461)
!465 = !DILocation(line: 22, column: 1, scope: !456)
!466 = distinct !DISubprogram(name: "sea_ipc_msg_handler", scope: !313, file: !313, line: 24, type: !285, scopeLine: 25, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !238, retainedNodes: !467)
!467 = !{!468, !469, !470, !471, !472, !474}
!468 = !DILocalVariable(name: "context", arg: 1, scope: !466, file: !313, line: 24, type: !275)
!469 = !DILocalVariable(name: "msg", arg: 2, scope: !466, file: !313, line: 24, type: !31)
!470 = !DILocalVariable(name: "msg_size", arg: 3, scope: !466, file: !313, line: 25, type: !33)
!471 = !DILocalVariable(name: "iov", scope: !466, file: !313, line: 27, type: !332)
!472 = !DILocalVariable(name: "i_msg", scope: !466, file: !313, line: 31, type: !473)
!473 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_msg_t", file: !6, line: 78, baseType: !327)
!474 = !DILocalVariable(name: "rc", scope: !466, file: !313, line: 35, type: !19)
!475 = !DILocation(line: 24, column: 60, scope: !466)
!476 = !DILocation(line: 24, column: 75, scope: !466)
!477 = !DILocation(line: 25, column: 39, scope: !466)
!478 = !DILocation(line: 27, column: 3, scope: !466)
!479 = !DILocation(line: 27, column: 16, scope: !466)
!480 = !DILocation(line: 27, column: 22, scope: !466)
!481 = !DILocation(line: 28, column: 19, scope: !466)
!482 = !{!483, !376, i64 0}
!483 = !{!"iovec", !376, i64 0, !360, i64 4}
!484 = !DILocation(line: 29, column: 18, scope: !466)
!485 = !{!483, !360, i64 4}
!486 = !DILocation(line: 31, column: 3, scope: !466)
!487 = !DILocation(line: 31, column: 13, scope: !466)
!488 = !DILocation(line: 31, column: 21, scope: !466)
!489 = !{!490, !360, i64 0}
!490 = !{!"ipc_msg", !360, i64 0, !376, i64 4, !360, i64 8, !376, i64 12}
!491 = !{!490, !376, i64 4}
!492 = !{!490, !360, i64 8}
!493 = !{!490, !376, i64 12}
!494 = !DILocation(line: 35, column: 3, scope: !466)
!495 = !DILocation(line: 35, column: 7, scope: !466)
!496 = !DILocation(line: 35, column: 21, scope: !466)
!497 = !DILocation(line: 35, column: 30, scope: !466)
!498 = !DILocation(line: 35, column: 37, scope: !466)
!499 = !{!444, !360, i64 4}
!500 = !DILocation(line: 35, column: 12, scope: !466)
!501 = !DILocation(line: 36, column: 7, scope: !502)
!502 = distinct !DILexicalBlock(scope: !466, file: !313, line: 36, column: 7)
!503 = !DILocation(line: 36, column: 10, scope: !502)
!504 = !DILocation(line: 36, column: 7, scope: !466)
!505 = !DILocation(line: 37, column: 12, scope: !506)
!506 = distinct !DILexicalBlock(scope: !502, file: !313, line: 36, column: 15)
!507 = !DILocation(line: 37, column: 5, scope: !506)
!508 = !DILocation(line: 39, column: 3, scope: !466)
!509 = !DILocation(line: 40, column: 1, scope: !466)
!510 = distinct !DISubprogram(name: "sync_ipc_send_msg", scope: !154, file: !154, line: 289, type: !511, scopeLine: 293, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !513)
!511 = !DISubroutineType(types: !512)
!512 = !{!19, !37, !27, !7, !27, !7}
!513 = !{!514, !515, !516, !517, !518, !519, !520, !522, !523, !524, !525, !527}
!514 = !DILocalVariable(name: "session", arg: 1, scope: !510, file: !154, line: 289, type: !37)
!515 = !DILocalVariable(name: "tx_iovecs", arg: 2, scope: !510, file: !154, line: 290, type: !27)
!516 = !DILocalVariable(name: "tx_iovec_count", arg: 3, scope: !510, file: !154, line: 291, type: !7)
!517 = !DILocalVariable(name: "rx_iovecs", arg: 4, scope: !510, file: !154, line: 292, type: !27)
!518 = !DILocalVariable(name: "rx_iovec_count", arg: 5, scope: !510, file: !154, line: 293, type: !7)
!519 = !DILocalVariable(name: "tx_msg", scope: !510, file: !154, line: 294, type: !21)
!520 = !DILocalVariable(name: "rc", scope: !510, file: !154, line: 299, type: !521)
!521 = !DIBasicType(name: "long int", size: 32, encoding: DW_ATE_signed)
!522 = !DILocalVariable(name: "inf", scope: !510, file: !154, line: 315, type: !109)
!523 = !DILocalVariable(name: "min_len", scope: !510, file: !154, line: 322, type: !33)
!524 = !DILocalVariable(name: "resp_size", scope: !510, file: !154, line: 330, type: !33)
!525 = !DILocalVariable(name: "i", scope: !526, file: !154, line: 331, type: !33)
!526 = distinct !DILexicalBlock(scope: !510, file: !154, line: 331, column: 5)
!527 = !DILocalVariable(name: "read_len", scope: !510, file: !154, line: 349, type: !33)
!528 = !DILocation(line: 289, column: 32, scope: !510)
!529 = !DILocation(line: 290, column: 37, scope: !510)
!530 = !DILocation(line: 291, column: 36, scope: !510)
!531 = !DILocation(line: 292, column: 37, scope: !510)
!532 = !DILocation(line: 293, column: 36, scope: !510)
!533 = !DILocation(line: 294, column: 5, scope: !510)
!534 = !DILocation(line: 294, column: 20, scope: !510)
!535 = !DILocation(line: 294, column: 29, scope: !510)
!536 = !DILocation(line: 296, column: 24, scope: !510)
!537 = !DILocation(line: 295, column: 20, scope: !510)
!538 = !DILocation(line: 299, column: 5, scope: !510)
!539 = !DILocation(line: 299, column: 10, scope: !510)
!540 = !DILocation(line: 299, column: 24, scope: !510)
!541 = !DILocation(line: 299, column: 15, scope: !510)
!542 = !{!543, !543, i64 0}
!543 = !{!"long", !361, i64 0}
!544 = !DILocation(line: 300, column: 9, scope: !545)
!545 = distinct !DILexicalBlock(scope: !510, file: !154, line: 300, column: 9)
!546 = !DILocation(line: 300, column: 12, scope: !545)
!547 = !DILocation(line: 300, column: 9, scope: !510)
!548 = !DILocation(line: 301, column: 27, scope: !549)
!549 = distinct !DILexicalBlock(scope: !545, file: !154, line: 300, column: 38)
!550 = !DILocation(line: 301, column: 14, scope: !549)
!551 = !DILocation(line: 301, column: 12, scope: !549)
!552 = !DILocation(line: 302, column: 5, scope: !549)
!553 = !DILocation(line: 304, column: 9, scope: !554)
!554 = distinct !DILexicalBlock(scope: !510, file: !154, line: 304, column: 9)
!555 = !DILocation(line: 304, column: 12, scope: !554)
!556 = !DILocation(line: 304, column: 9, scope: !510)
!557 = !DILocation(line: 305, column: 9, scope: !558)
!558 = distinct !DILexicalBlock(scope: !554, file: !154, line: 304, column: 17)
!559 = !DILocation(line: 305, column: 9, scope: !560)
!560 = distinct !DILexicalBlock(scope: !561, file: !154, line: 305, column: 9)
!561 = distinct !DILexicalBlock(scope: !562, file: !154, line: 305, column: 9)
!562 = distinct !DILexicalBlock(scope: !558, file: !154, line: 305, column: 9)
!563 = !DILocation(line: 305, column: 9, scope: !564)
!564 = distinct !DILexicalBlock(scope: !560, file: !154, line: 305, column: 9)
!565 = !DILocation(line: 305, column: 9, scope: !562)
!566 = !DILocation(line: 306, column: 16, scope: !558)
!567 = !DILocation(line: 306, column: 9, scope: !558)
!568 = !DILocation(line: 309, column: 9, scope: !569)
!569 = distinct !DILexicalBlock(scope: !510, file: !154, line: 309, column: 9)
!570 = !DILocation(line: 309, column: 19, scope: !569)
!571 = !DILocation(line: 309, column: 27, scope: !569)
!572 = !DILocation(line: 309, column: 30, scope: !569)
!573 = !DILocation(line: 309, column: 45, scope: !569)
!574 = !DILocation(line: 309, column: 9, scope: !510)
!575 = !DILocation(line: 310, column: 9, scope: !576)
!576 = distinct !DILexicalBlock(scope: !569, file: !154, line: 309, column: 51)
!577 = !DILocation(line: 311, column: 9, scope: !576)
!578 = !DILocation(line: 312, column: 9, scope: !576)
!579 = !DILocation(line: 315, column: 5, scope: !510)
!580 = !DILocation(line: 315, column: 25, scope: !510)
!581 = !DILocation(line: 316, column: 25, scope: !510)
!582 = !DILocation(line: 316, column: 10, scope: !510)
!583 = !DILocation(line: 316, column: 8, scope: !510)
!584 = !DILocation(line: 317, column: 9, scope: !585)
!585 = distinct !DILexicalBlock(scope: !510, file: !154, line: 317, column: 9)
!586 = !DILocation(line: 317, column: 12, scope: !585)
!587 = !DILocation(line: 317, column: 9, scope: !510)
!588 = !DILocation(line: 318, column: 9, scope: !589)
!589 = distinct !DILexicalBlock(scope: !585, file: !154, line: 317, column: 17)
!590 = !DILocation(line: 318, column: 9, scope: !591)
!591 = distinct !DILexicalBlock(scope: !592, file: !154, line: 318, column: 9)
!592 = distinct !DILexicalBlock(scope: !593, file: !154, line: 318, column: 9)
!593 = distinct !DILexicalBlock(scope: !589, file: !154, line: 318, column: 9)
!594 = !DILocation(line: 318, column: 9, scope: !595)
!595 = distinct !DILexicalBlock(scope: !591, file: !154, line: 318, column: 9)
!596 = !DILocation(line: 318, column: 9, scope: !593)
!597 = !DILocation(line: 319, column: 16, scope: !589)
!598 = !DILocation(line: 319, column: 9, scope: !589)
!599 = !DILocation(line: 322, column: 5, scope: !510)
!600 = !DILocation(line: 322, column: 12, scope: !510)
!601 = !DILocation(line: 322, column: 22, scope: !510)
!602 = !DILocation(line: 322, column: 35, scope: !510)
!603 = !DILocation(line: 323, column: 13, scope: !604)
!604 = distinct !DILexicalBlock(scope: !510, file: !154, line: 323, column: 9)
!605 = !{!606, !360, i64 0}
!606 = !{!"ipc_msg_info", !360, i64 0, !360, i64 4, !360, i64 8}
!607 = !DILocation(line: 323, column: 19, scope: !604)
!608 = !DILocation(line: 323, column: 17, scope: !604)
!609 = !DILocation(line: 323, column: 9, scope: !510)
!610 = !DILocation(line: 324, column: 9, scope: !611)
!611 = distinct !DILexicalBlock(scope: !604, file: !154, line: 323, column: 28)
!612 = !DILocation(line: 324, column: 9, scope: !613)
!613 = distinct !DILexicalBlock(scope: !614, file: !154, line: 324, column: 9)
!614 = distinct !DILexicalBlock(scope: !615, file: !154, line: 324, column: 9)
!615 = distinct !DILexicalBlock(scope: !611, file: !154, line: 324, column: 9)
!616 = !DILocation(line: 324, column: 9, scope: !617)
!617 = distinct !DILexicalBlock(scope: !613, file: !154, line: 324, column: 9)
!618 = !DILocation(line: 324, column: 9, scope: !615)
!619 = !DILocation(line: 325, column: 17, scope: !611)
!620 = !DILocation(line: 325, column: 30, scope: !611)
!621 = !{!606, !360, i64 4}
!622 = !DILocation(line: 325, column: 9, scope: !611)
!623 = !DILocation(line: 326, column: 9, scope: !611)
!624 = !DILocation(line: 330, column: 5, scope: !510)
!625 = !DILocation(line: 330, column: 12, scope: !510)
!626 = !DILocation(line: 331, column: 10, scope: !526)
!627 = !DILocation(line: 331, column: 17, scope: !526)
!628 = !DILocation(line: 331, column: 24, scope: !629)
!629 = distinct !DILexicalBlock(scope: !526, file: !154, line: 331, column: 5)
!630 = !DILocation(line: 331, column: 28, scope: !629)
!631 = !DILocation(line: 331, column: 26, scope: !629)
!632 = !DILocation(line: 331, column: 5, scope: !526)
!633 = !DILocation(line: 331, column: 5, scope: !629)
!634 = !DILocation(line: 332, column: 22, scope: !635)
!635 = distinct !DILexicalBlock(scope: !629, file: !154, line: 331, column: 49)
!636 = !DILocation(line: 332, column: 32, scope: !635)
!637 = !DILocation(line: 332, column: 35, scope: !635)
!638 = !DILocation(line: 332, column: 19, scope: !635)
!639 = !DILocation(line: 333, column: 5, scope: !635)
!640 = !DILocation(line: 331, column: 44, scope: !629)
!641 = distinct !{!641, !632, !642}
!642 = !DILocation(line: 333, column: 5, scope: !526)
!643 = !DILocation(line: 335, column: 9, scope: !644)
!644 = distinct !DILexicalBlock(scope: !510, file: !154, line: 335, column: 9)
!645 = !DILocation(line: 335, column: 25, scope: !644)
!646 = !DILocation(line: 335, column: 19, scope: !644)
!647 = !DILocation(line: 335, column: 9, scope: !510)
!648 = !DILocation(line: 336, column: 9, scope: !649)
!649 = distinct !DILexicalBlock(scope: !644, file: !154, line: 335, column: 30)
!650 = !DILocation(line: 336, column: 9, scope: !651)
!651 = distinct !DILexicalBlock(scope: !652, file: !154, line: 336, column: 9)
!652 = distinct !DILexicalBlock(scope: !653, file: !154, line: 336, column: 9)
!653 = distinct !DILexicalBlock(scope: !649, file: !154, line: 336, column: 9)
!654 = !DILocation(line: 336, column: 9, scope: !655)
!655 = distinct !DILexicalBlock(scope: !651, file: !154, line: 336, column: 9)
!656 = !DILocation(line: 336, column: 9, scope: !653)
!657 = !DILocation(line: 338, column: 17, scope: !649)
!658 = !DILocation(line: 338, column: 30, scope: !649)
!659 = !DILocation(line: 338, column: 9, scope: !649)
!660 = !DILocation(line: 339, column: 9, scope: !649)
!661 = !DILocation(line: 342, column: 24, scope: !510)
!662 = !DILocation(line: 342, column: 37, scope: !510)
!663 = !DILocation(line: 342, column: 41, scope: !510)
!664 = !DILocation(line: 342, column: 52, scope: !510)
!665 = !DILocation(line: 342, column: 10, scope: !510)
!666 = !DILocation(line: 342, column: 8, scope: !510)
!667 = !DILocation(line: 343, column: 13, scope: !510)
!668 = !DILocation(line: 343, column: 26, scope: !510)
!669 = !DILocation(line: 343, column: 5, scope: !510)
!670 = !DILocation(line: 344, column: 9, scope: !671)
!671 = distinct !DILexicalBlock(scope: !510, file: !154, line: 344, column: 9)
!672 = !DILocation(line: 344, column: 12, scope: !671)
!673 = !DILocation(line: 344, column: 9, scope: !510)
!674 = !DILocation(line: 345, column: 9, scope: !675)
!675 = distinct !DILexicalBlock(scope: !671, file: !154, line: 344, column: 17)
!676 = !DILocation(line: 345, column: 9, scope: !677)
!677 = distinct !DILexicalBlock(scope: !678, file: !154, line: 345, column: 9)
!678 = distinct !DILexicalBlock(scope: !679, file: !154, line: 345, column: 9)
!679 = distinct !DILexicalBlock(scope: !675, file: !154, line: 345, column: 9)
!680 = !DILocation(line: 345, column: 9, scope: !681)
!681 = distinct !DILexicalBlock(scope: !677, file: !154, line: 345, column: 9)
!682 = !DILocation(line: 345, column: 9, scope: !679)
!683 = !DILocation(line: 346, column: 16, scope: !675)
!684 = !DILocation(line: 346, column: 9, scope: !675)
!685 = !DILocation(line: 349, column: 5, scope: !510)
!686 = !DILocation(line: 349, column: 12, scope: !510)
!687 = !DILocation(line: 349, column: 31, scope: !510)
!688 = !DILocation(line: 350, column: 9, scope: !689)
!689 = distinct !DILexicalBlock(scope: !510, file: !154, line: 350, column: 9)
!690 = !DILocation(line: 350, column: 25, scope: !689)
!691 = !DILocation(line: 350, column: 18, scope: !689)
!692 = !DILocation(line: 350, column: 9, scope: !510)
!693 = !DILocation(line: 352, column: 9, scope: !694)
!694 = distinct !DILexicalBlock(scope: !689, file: !154, line: 350, column: 30)
!695 = !DILocation(line: 352, column: 9, scope: !696)
!696 = distinct !DILexicalBlock(scope: !697, file: !154, line: 352, column: 9)
!697 = distinct !DILexicalBlock(scope: !698, file: !154, line: 352, column: 9)
!698 = distinct !DILexicalBlock(scope: !694, file: !154, line: 352, column: 9)
!699 = !DILocation(line: 352, column: 9, scope: !700)
!700 = distinct !DILexicalBlock(scope: !696, file: !154, line: 352, column: 9)
!701 = !DILocation(line: 352, column: 9, scope: !698)
!702 = !DILocation(line: 353, column: 9, scope: !694)
!703 = !DILocation(line: 356, column: 12, scope: !510)
!704 = !DILocation(line: 356, column: 5, scope: !510)
!705 = !DILocation(line: 357, column: 1, scope: !510)
!706 = distinct !DISubprogram(name: "wait_to_send", scope: !154, file: !154, line: 264, type: !707, scopeLine: 264, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !709)
!707 = !DISubroutineType(types: !708)
!708 = !{!19, !37, !20}
!709 = !{!710, !711, !712, !713}
!710 = !DILocalVariable(name: "session", arg: 1, scope: !706, file: !154, line: 264, type: !37)
!711 = !DILocalVariable(name: "msg", arg: 2, scope: !706, file: !154, line: 264, type: !20)
!712 = !DILocalVariable(name: "rc", scope: !706, file: !154, line: 265, type: !19)
!713 = !DILocalVariable(name: "ev", scope: !706, file: !154, line: 266, type: !70)
!714 = !DILocation(line: 264, column: 34, scope: !706)
!715 = !DILocation(line: 264, column: 59, scope: !706)
!716 = !DILocation(line: 265, column: 5, scope: !706)
!717 = !DILocation(line: 265, column: 9, scope: !706)
!718 = !DILocation(line: 266, column: 5, scope: !706)
!719 = !DILocation(line: 266, column: 19, scope: !706)
!720 = !DILocation(line: 268, column: 15, scope: !706)
!721 = !DILocation(line: 268, column: 10, scope: !706)
!722 = !DILocation(line: 268, column: 8, scope: !706)
!723 = !DILocation(line: 269, column: 9, scope: !724)
!724 = distinct !DILexicalBlock(scope: !706, file: !154, line: 269, column: 9)
!725 = !DILocation(line: 269, column: 12, scope: !724)
!726 = !DILocation(line: 269, column: 9, scope: !706)
!727 = !DILocation(line: 270, column: 9, scope: !728)
!728 = distinct !DILexicalBlock(scope: !724, file: !154, line: 269, column: 17)
!729 = !DILocation(line: 270, column: 9, scope: !730)
!730 = distinct !DILexicalBlock(scope: !731, file: !154, line: 270, column: 9)
!731 = distinct !DILexicalBlock(scope: !732, file: !154, line: 270, column: 9)
!732 = distinct !DILexicalBlock(scope: !728, file: !154, line: 270, column: 9)
!733 = !DILocation(line: 270, column: 9, scope: !734)
!734 = distinct !DILexicalBlock(scope: !730, file: !154, line: 270, column: 9)
!735 = !DILocation(line: 270, column: 9, scope: !732)
!736 = !DILocation(line: 271, column: 16, scope: !728)
!737 = !DILocation(line: 271, column: 9, scope: !728)
!738 = !DILocation(line: 274, column: 12, scope: !739)
!739 = distinct !DILexicalBlock(scope: !706, file: !154, line: 274, column: 9)
!740 = !DILocation(line: 274, column: 18, scope: !739)
!741 = !DILocation(line: 274, column: 9, scope: !706)
!742 = !DILocation(line: 275, column: 25, scope: !743)
!743 = distinct !DILexicalBlock(scope: !739, file: !154, line: 274, column: 52)
!744 = !DILocation(line: 275, column: 34, scope: !743)
!745 = !DILocation(line: 275, column: 16, scope: !743)
!746 = !DILocation(line: 275, column: 9, scope: !743)
!747 = !DILocation(line: 278, column: 12, scope: !748)
!748 = distinct !DILexicalBlock(scope: !706, file: !154, line: 278, column: 9)
!749 = !DILocation(line: 278, column: 18, scope: !748)
!750 = !DILocation(line: 278, column: 9, scope: !706)
!751 = !DILocation(line: 279, column: 9, scope: !752)
!752 = distinct !DILexicalBlock(scope: !748, file: !154, line: 278, column: 41)
!753 = !DILocation(line: 282, column: 12, scope: !754)
!754 = distinct !DILexicalBlock(scope: !706, file: !154, line: 282, column: 9)
!755 = !DILocation(line: 282, column: 18, scope: !754)
!756 = !DILocation(line: 282, column: 9, scope: !706)
!757 = !DILocation(line: 283, column: 9, scope: !758)
!758 = distinct !DILexicalBlock(scope: !754, file: !154, line: 282, column: 41)
!759 = !DILocation(line: 286, column: 12, scope: !706)
!760 = !DILocation(line: 286, column: 5, scope: !706)
!761 = !DILocation(line: 287, column: 1, scope: !706)
!762 = distinct !DISubprogram(name: "unittest_printf", scope: !763, file: !763, line: 24, type: !764, scopeLine: 24, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !766)
!763 = !DIFile(filename: "trusty/user/base/include/user/trusty_log.h", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!764 = !DISubroutineType(types: !765)
!765 = !{!19, !46, null}
!766 = !{!767}
!767 = !DILocalVariable(name: "fmt", arg: 1, scope: !762, file: !763, line: 24, type: !46)
!768 = !DILocation(line: 24, column: 47, scope: !762)
!769 = !DILocation(line: 25, column: 5, scope: !762)
!770 = distinct !DISubprogram(name: "await_response", scope: !154, file: !154, line: 248, type: !771, scopeLine: 248, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !773)
!771 = !DISubroutineType(types: !772)
!772 = !{!19, !37, !108}
!773 = !{!774, !775, !776, !778}
!774 = !DILocalVariable(name: "session", arg: 1, scope: !770, file: !154, line: 248, type: !37)
!775 = !DILocalVariable(name: "inf", arg: 2, scope: !770, file: !154, line: 248, type: !108)
!776 = !DILocalVariable(name: "uevt", scope: !770, file: !154, line: 249, type: !777)
!777 = !DIDerivedType(tag: DW_TAG_typedef, name: "uevent_t", file: !6, line: 116, baseType: !70)
!778 = !DILocalVariable(name: "rc", scope: !770, file: !154, line: 250, type: !521)
!779 = !DILocation(line: 248, column: 36, scope: !770)
!780 = !DILocation(line: 248, column: 66, scope: !770)
!781 = !DILocation(line: 249, column: 5, scope: !770)
!782 = !DILocation(line: 249, column: 14, scope: !770)
!783 = !DILocation(line: 250, column: 5, scope: !770)
!784 = !DILocation(line: 250, column: 10, scope: !770)
!785 = !DILocation(line: 250, column: 20, scope: !770)
!786 = !DILocation(line: 250, column: 15, scope: !770)
!787 = !DILocation(line: 251, column: 9, scope: !788)
!788 = distinct !DILexicalBlock(scope: !770, file: !154, line: 251, column: 9)
!789 = !DILocation(line: 251, column: 12, scope: !788)
!790 = !DILocation(line: 251, column: 9, scope: !770)
!791 = !DILocation(line: 252, column: 9, scope: !792)
!792 = distinct !DILexicalBlock(scope: !788, file: !154, line: 251, column: 25)
!793 = !DILocation(line: 252, column: 9, scope: !794)
!794 = distinct !DILexicalBlock(scope: !795, file: !154, line: 252, column: 9)
!795 = distinct !DILexicalBlock(scope: !796, file: !154, line: 252, column: 9)
!796 = distinct !DILexicalBlock(scope: !792, file: !154, line: 252, column: 9)
!797 = !DILocation(line: 252, column: 9, scope: !798)
!798 = distinct !DILexicalBlock(scope: !794, file: !154, line: 252, column: 9)
!799 = !DILocation(line: 252, column: 9, scope: !796)
!800 = !DILocation(line: 253, column: 16, scope: !792)
!801 = !DILocation(line: 253, column: 9, scope: !792)
!802 = !DILocation(line: 256, column: 18, scope: !770)
!803 = !DILocation(line: 256, column: 27, scope: !770)
!804 = !DILocation(line: 256, column: 10, scope: !770)
!805 = !DILocation(line: 256, column: 8, scope: !770)
!806 = !DILocation(line: 257, column: 9, scope: !807)
!807 = distinct !DILexicalBlock(scope: !770, file: !154, line: 257, column: 9)
!808 = !DILocation(line: 257, column: 12, scope: !807)
!809 = !DILocation(line: 257, column: 9, scope: !770)
!810 = !DILocation(line: 258, column: 9, scope: !811)
!811 = distinct !DILexicalBlock(scope: !807, file: !154, line: 257, column: 25)
!812 = !DILocation(line: 258, column: 9, scope: !813)
!813 = distinct !DILexicalBlock(scope: !814, file: !154, line: 258, column: 9)
!814 = distinct !DILexicalBlock(scope: !815, file: !154, line: 258, column: 9)
!815 = distinct !DILexicalBlock(scope: !811, file: !154, line: 258, column: 9)
!816 = !DILocation(line: 258, column: 9, scope: !817)
!817 = distinct !DILexicalBlock(scope: !813, file: !154, line: 258, column: 9)
!818 = !DILocation(line: 258, column: 9, scope: !815)
!819 = !DILocation(line: 259, column: 5, scope: !811)
!820 = !DILocation(line: 261, column: 12, scope: !770)
!821 = !DILocation(line: 261, column: 5, scope: !770)
!822 = !DILocation(line: 262, column: 1, scope: !770)
!823 = distinct !DISubprogram(name: "read_response", scope: !154, file: !154, line: 228, type: !824, scopeLine: 231, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !826)
!824 = !DISubroutineType(types: !825)
!825 = !{!19, !37, !24, !27, !33}
!826 = !{!827, !828, !829, !830, !831, !832, !833}
!827 = !DILocalVariable(name: "session", arg: 1, scope: !823, file: !154, line: 228, type: !37)
!828 = !DILocalVariable(name: "msg_id", arg: 2, scope: !823, file: !154, line: 229, type: !24)
!829 = !DILocalVariable(name: "iovecs", arg: 3, scope: !823, file: !154, line: 230, type: !27)
!830 = !DILocalVariable(name: "iovec_count", arg: 4, scope: !823, file: !154, line: 231, type: !33)
!831 = !DILocalVariable(name: "rx_msg", scope: !823, file: !154, line: 232, type: !21)
!832 = !DILocalVariable(name: "rc", scope: !823, file: !154, line: 237, type: !521)
!833 = !DILocalVariable(name: "read_size", scope: !823, file: !154, line: 244, type: !33)
!834 = !DILocation(line: 228, column: 35, scope: !823)
!835 = !DILocation(line: 229, column: 35, scope: !823)
!836 = !DILocation(line: 230, column: 40, scope: !823)
!837 = !DILocation(line: 231, column: 33, scope: !823)
!838 = !DILocation(line: 232, column: 5, scope: !823)
!839 = !DILocation(line: 232, column: 20, scope: !823)
!840 = !DILocation(line: 232, column: 29, scope: !823)
!841 = !DILocation(line: 234, column: 24, scope: !823)
!842 = !DILocation(line: 233, column: 20, scope: !823)
!843 = !DILocation(line: 237, column: 5, scope: !823)
!844 = !DILocation(line: 237, column: 10, scope: !823)
!845 = !DILocation(line: 237, column: 24, scope: !823)
!846 = !DILocation(line: 237, column: 33, scope: !823)
!847 = !DILocation(line: 237, column: 15, scope: !823)
!848 = !DILocation(line: 238, column: 13, scope: !823)
!849 = !DILocation(line: 238, column: 22, scope: !823)
!850 = !DILocation(line: 238, column: 5, scope: !823)
!851 = !DILocation(line: 239, column: 9, scope: !852)
!852 = distinct !DILexicalBlock(scope: !823, file: !154, line: 239, column: 9)
!853 = !DILocation(line: 239, column: 12, scope: !852)
!854 = !DILocation(line: 239, column: 9, scope: !823)
!855 = !DILocation(line: 240, column: 9, scope: !856)
!856 = distinct !DILexicalBlock(scope: !852, file: !154, line: 239, column: 17)
!857 = !DILocation(line: 240, column: 9, scope: !858)
!858 = distinct !DILexicalBlock(scope: !859, file: !154, line: 240, column: 9)
!859 = distinct !DILexicalBlock(scope: !860, file: !154, line: 240, column: 9)
!860 = distinct !DILexicalBlock(scope: !856, file: !154, line: 240, column: 9)
!861 = !DILocation(line: 240, column: 9, scope: !862)
!862 = distinct !DILexicalBlock(scope: !858, file: !154, line: 240, column: 9)
!863 = !DILocation(line: 240, column: 9, scope: !860)
!864 = !DILocation(line: 241, column: 16, scope: !856)
!865 = !DILocation(line: 241, column: 9, scope: !856)
!866 = !DILocation(line: 244, column: 5, scope: !823)
!867 = !DILocation(line: 244, column: 12, scope: !823)
!868 = !DILocation(line: 244, column: 32, scope: !823)
!869 = !DILocation(line: 245, column: 12, scope: !823)
!870 = !DILocation(line: 245, column: 5, scope: !823)
!871 = !DILocation(line: 246, column: 1, scope: !823)
!872 = distinct !DISubprogram(name: "dispatch_event", scope: !154, file: !154, line: 359, type: !873, scopeLine: 359, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !877)
!873 = !DISubroutineType(types: !874)
!874 = !{null, !875}
!875 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !876, size: 32)
!876 = !DIDerivedType(tag: DW_TAG_const_type, baseType: !777)
!877 = !{!878, !879}
!878 = !DILocalVariable(name: "ev", arg: 1, scope: !872, file: !154, line: 359, type: !875)
!879 = !DILocalVariable(name: "context", scope: !872, file: !154, line: 366, type: !67)
!880 = !DILocation(line: 359, column: 37, scope: !872)
!881 = !DILocation(line: 360, column: 5, scope: !872)
!882 = !DILocation(line: 362, column: 9, scope: !883)
!883 = distinct !DILexicalBlock(scope: !872, file: !154, line: 362, column: 9)
!884 = !DILocation(line: 362, column: 13, scope: !883)
!885 = !DILocation(line: 362, column: 19, scope: !883)
!886 = !DILocation(line: 362, column: 9, scope: !872)
!887 = !DILocation(line: 363, column: 9, scope: !888)
!888 = distinct !DILexicalBlock(scope: !883, file: !154, line: 362, column: 44)
!889 = !DILocation(line: 366, column: 5, scope: !872)
!890 = !DILocation(line: 366, column: 25, scope: !872)
!891 = !DILocation(line: 366, column: 35, scope: !872)
!892 = !DILocation(line: 366, column: 39, scope: !872)
!893 = !DILocation(line: 367, column: 5, scope: !872)
!894 = !DILocation(line: 368, column: 5, scope: !872)
!895 = !{!445, !376, i64 0}
!896 = !DILocation(line: 369, column: 5, scope: !872)
!897 = !{!445, !360, i64 4}
!898 = !DILocation(line: 371, column: 5, scope: !872)
!899 = !DILocation(line: 371, column: 14, scope: !872)
!900 = !DILocation(line: 371, column: 26, scope: !872)
!901 = !DILocation(line: 371, column: 35, scope: !872)
!902 = !DILocation(line: 372, column: 1, scope: !872)
!903 = distinct !DISubprogram(name: "ipc_port_create", scope: !154, file: !154, line: 374, type: !904, scopeLine: 378, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !906)
!904 = !DISubroutineType(types: !905)
!905 = !{!19, !117, !46, !33, !33, !24}
!906 = !{!907, !908, !909, !910, !911, !912, !913, !914, !915}
!907 = !DILocalVariable(name: "ctxp", arg: 1, scope: !903, file: !154, line: 374, type: !117)
!908 = !DILocalVariable(name: "port_name", arg: 2, scope: !903, file: !154, line: 375, type: !46)
!909 = !DILocalVariable(name: "queue_size", arg: 3, scope: !903, file: !154, line: 376, type: !33)
!910 = !DILocalVariable(name: "max_buffer_size", arg: 4, scope: !903, file: !154, line: 377, type: !33)
!911 = !DILocalVariable(name: "flags", arg: 5, scope: !903, file: !154, line: 378, type: !24)
!912 = !DILocalVariable(name: "rc", scope: !903, file: !154, line: 379, type: !19)
!913 = !DILocalVariable(name: "port_handle", scope: !903, file: !154, line: 390, type: !37)
!914 = !DILabel(scope: !903, name: "err_set_cookie", file: !154, line: 409)
!915 = !DILabel(scope: !903, name: "err_grow_msg", file: !154, line: 410)
!916 = !DILocation(line: 374, column: 46, scope: !903)
!917 = !DILocation(line: 375, column: 33, scope: !903)
!918 = !DILocation(line: 376, column: 28, scope: !903)
!919 = !DILocation(line: 377, column: 28, scope: !903)
!920 = !DILocation(line: 378, column: 30, scope: !903)
!921 = !DILocation(line: 379, column: 5, scope: !903)
!922 = !DILocation(line: 379, column: 9, scope: !903)
!923 = !DILocation(line: 380, column: 5, scope: !903)
!924 = !DILocation(line: 381, column: 5, scope: !903)
!925 = !DILocation(line: 383, column: 22, scope: !903)
!926 = !DILocation(line: 383, column: 33, scope: !903)
!927 = !DILocation(line: 383, column: 45, scope: !903)
!928 = !DILocation(line: 383, column: 62, scope: !903)
!929 = !DILocation(line: 383, column: 10, scope: !903)
!930 = !DILocation(line: 383, column: 8, scope: !903)
!931 = !DILocation(line: 385, column: 9, scope: !932)
!932 = distinct !DILexicalBlock(scope: !903, file: !154, line: 385, column: 9)
!933 = !DILocation(line: 385, column: 12, scope: !932)
!934 = !DILocation(line: 385, column: 9, scope: !903)
!935 = !DILocation(line: 386, column: 9, scope: !936)
!936 = distinct !DILexicalBlock(scope: !932, file: !154, line: 385, column: 17)
!937 = !DILocation(line: 386, column: 9, scope: !938)
!938 = distinct !DILexicalBlock(scope: !939, file: !154, line: 386, column: 9)
!939 = distinct !DILexicalBlock(scope: !940, file: !154, line: 386, column: 9)
!940 = distinct !DILexicalBlock(scope: !936, file: !154, line: 386, column: 9)
!941 = !DILocation(line: 386, column: 9, scope: !942)
!942 = distinct !DILexicalBlock(scope: !938, file: !154, line: 386, column: 9)
!943 = !DILocation(line: 386, column: 9, scope: !940)
!944 = !DILocation(line: 387, column: 16, scope: !936)
!945 = !DILocation(line: 387, column: 9, scope: !936)
!946 = !DILocation(line: 390, column: 5, scope: !903)
!947 = !DILocation(line: 390, column: 14, scope: !903)
!948 = !DILocation(line: 390, column: 38, scope: !903)
!949 = !DILocation(line: 391, column: 21, scope: !903)
!950 = !DILocation(line: 391, column: 34, scope: !903)
!951 = !DILocation(line: 391, column: 10, scope: !903)
!952 = !DILocation(line: 391, column: 8, scope: !903)
!953 = !DILocation(line: 392, column: 9, scope: !954)
!954 = distinct !DILexicalBlock(scope: !903, file: !154, line: 392, column: 9)
!955 = !DILocation(line: 392, column: 12, scope: !954)
!956 = !DILocation(line: 392, column: 9, scope: !903)
!957 = !DILocation(line: 393, column: 9, scope: !958)
!958 = distinct !DILexicalBlock(scope: !954, file: !154, line: 392, column: 17)
!959 = !DILocation(line: 393, column: 9, scope: !960)
!960 = distinct !DILexicalBlock(scope: !961, file: !154, line: 393, column: 9)
!961 = distinct !DILexicalBlock(scope: !962, file: !154, line: 393, column: 9)
!962 = distinct !DILexicalBlock(scope: !958, file: !154, line: 393, column: 9)
!963 = !DILocation(line: 393, column: 9, scope: !964)
!964 = distinct !DILexicalBlock(scope: !960, file: !154, line: 393, column: 9)
!965 = !DILocation(line: 393, column: 9, scope: !962)
!966 = !DILocation(line: 394, column: 9, scope: !958)
!967 = !DILocation(line: 397, column: 29, scope: !903)
!968 = !DILocation(line: 397, column: 10, scope: !903)
!969 = !DILocation(line: 397, column: 8, scope: !903)
!970 = !DILocation(line: 398, column: 9, scope: !971)
!971 = distinct !DILexicalBlock(scope: !903, file: !154, line: 398, column: 9)
!972 = !DILocation(line: 398, column: 12, scope: !971)
!973 = !DILocation(line: 398, column: 9, scope: !903)
!974 = !DILocation(line: 399, column: 9, scope: !975)
!975 = distinct !DILexicalBlock(scope: !971, file: !154, line: 398, column: 17)
!976 = !DILocation(line: 399, column: 9, scope: !977)
!977 = distinct !DILexicalBlock(scope: !978, file: !154, line: 399, column: 9)
!978 = distinct !DILexicalBlock(scope: !979, file: !154, line: 399, column: 9)
!979 = distinct !DILexicalBlock(scope: !975, file: !154, line: 399, column: 9)
!980 = !DILocation(line: 399, column: 9, scope: !981)
!981 = distinct !DILexicalBlock(scope: !977, file: !154, line: 399, column: 9)
!982 = !DILocation(line: 399, column: 9, scope: !979)
!983 = !DILocation(line: 401, column: 9, scope: !975)
!984 = !DILocation(line: 404, column: 27, scope: !903)
!985 = !DILocation(line: 404, column: 5, scope: !903)
!986 = !DILocation(line: 404, column: 11, scope: !903)
!987 = !DILocation(line: 404, column: 18, scope: !903)
!988 = !DILocation(line: 404, column: 25, scope: !903)
!989 = !{!990, !360, i64 4}
!990 = !{!"ipc_port_context", !445, i64 0, !991, i64 8, !447, i64 12}
!991 = !{!"ipc_port_ops", !376, i64 0}
!992 = !DILocation(line: 405, column: 5, scope: !903)
!993 = !DILocation(line: 405, column: 11, scope: !903)
!994 = !DILocation(line: 405, column: 18, scope: !903)
!995 = !DILocation(line: 405, column: 30, scope: !903)
!996 = !{!990, !376, i64 0}
!997 = !DILocation(line: 406, column: 22, scope: !903)
!998 = !DILocation(line: 406, column: 28, scope: !903)
!999 = !DILocation(line: 406, column: 5, scope: !903)
!1000 = !DILocation(line: 407, column: 5, scope: !903)
!1001 = !DILocation(line: 409, column: 1, scope: !903)
!1002 = !DILocation(line: 410, column: 1, scope: !903)
!1003 = !DILocation(line: 411, column: 11, scope: !903)
!1004 = !DILocation(line: 411, column: 5, scope: !903)
!1005 = !DILocation(line: 412, column: 12, scope: !903)
!1006 = !DILocation(line: 412, column: 5, scope: !903)
!1007 = !DILocation(line: 413, column: 1, scope: !903)
!1008 = distinct !DISubprogram(name: "is_valid_port_ops", scope: !154, file: !154, line: 68, type: !1009, scopeLine: 68, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1012)
!1009 = !DISubroutineType(types: !1010)
!1010 = !{!19, !1011}
!1011 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !122, size: 32)
!1012 = !{!1013}
!1013 = !DILocalVariable(name: "ops", arg: 1, scope: !1008, file: !154, line: 68, type: !1011)
!1014 = !DILocation(line: 68, column: 51, scope: !1008)
!1015 = !DILocation(line: 69, column: 13, scope: !1008)
!1016 = !DILocation(line: 69, column: 18, scope: !1008)
!1017 = !{!991, !376, i64 0}
!1018 = !DILocation(line: 69, column: 29, scope: !1008)
!1019 = !DILocation(line: 69, column: 5, scope: !1008)
!1020 = distinct !DISubprogram(name: "maybe_grow_msg_buf", scope: !154, file: !154, line: 37, type: !1021, scopeLine: 37, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1023)
!1021 = !DISubroutineType(types: !1022)
!1022 = !{!19, !33}
!1023 = !{!1024, !1025}
!1024 = !DILocalVariable(name: "new_max_size", arg: 1, scope: !1020, file: !154, line: 37, type: !33)
!1025 = !DILocalVariable(name: "tmp", scope: !1026, file: !154, line: 39, type: !1028)
!1026 = distinct !DILexicalBlock(scope: !1027, file: !154, line: 38, column: 38)
!1027 = distinct !DILexicalBlock(scope: !1020, file: !154, line: 38, column: 9)
!1028 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !142, size: 32)
!1029 = !DILocation(line: 37, column: 38, scope: !1020)
!1030 = !DILocation(line: 38, column: 9, scope: !1027)
!1031 = !DILocation(line: 38, column: 24, scope: !1027)
!1032 = !DILocation(line: 38, column: 22, scope: !1027)
!1033 = !DILocation(line: 38, column: 9, scope: !1020)
!1034 = !DILocation(line: 39, column: 9, scope: !1026)
!1035 = !DILocation(line: 39, column: 18, scope: !1026)
!1036 = !DILocation(line: 39, column: 32, scope: !1026)
!1037 = !DILocation(line: 39, column: 41, scope: !1026)
!1038 = !DILocation(line: 39, column: 24, scope: !1026)
!1039 = !DILocation(line: 40, column: 13, scope: !1040)
!1040 = distinct !DILexicalBlock(scope: !1026, file: !154, line: 40, column: 13)
!1041 = !DILocation(line: 40, column: 17, scope: !1040)
!1042 = !DILocation(line: 40, column: 13, scope: !1026)
!1043 = !DILocation(line: 41, column: 13, scope: !1044)
!1044 = distinct !DILexicalBlock(scope: !1040, file: !154, line: 40, column: 26)
!1045 = !DILocation(line: 43, column: 19, scope: !1026)
!1046 = !DILocation(line: 43, column: 17, scope: !1026)
!1047 = !DILocation(line: 44, column: 24, scope: !1026)
!1048 = !DILocation(line: 44, column: 22, scope: !1026)
!1049 = !DILocation(line: 45, column: 5, scope: !1027)
!1050 = !DILocation(line: 45, column: 5, scope: !1026)
!1051 = !DILocation(line: 46, column: 5, scope: !1020)
!1052 = !DILocation(line: 47, column: 1, scope: !1020)
!1053 = distinct !DISubprogram(name: "handle_port", scope: !154, file: !154, line: 190, type: !65, scopeLine: 190, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1054)
!1054 = !{!1055, !1056, !1057}
!1055 = !DILocalVariable(name: "ctx", arg: 1, scope: !1053, file: !154, line: 190, type: !67)
!1056 = !DILocalVariable(name: "ev", arg: 2, scope: !1053, file: !154, line: 190, type: !68)
!1057 = !DILocalVariable(name: "port_ctx", scope: !1053, file: !154, line: 191, type: !117)
!1058 = !DILocation(line: 190, column: 45, scope: !1053)
!1059 = !DILocation(line: 190, column: 71, scope: !1053)
!1060 = !DILocation(line: 191, column: 5, scope: !1053)
!1061 = !DILocation(line: 191, column: 30, scope: !1053)
!1062 = !DILocation(line: 191, column: 57, scope: !1053)
!1063 = !DILocation(line: 191, column: 41, scope: !1053)
!1064 = !DILocation(line: 192, column: 5, scope: !1053)
!1065 = !DILocation(line: 194, column: 24, scope: !1053)
!1066 = !DILocation(line: 194, column: 5, scope: !1053)
!1067 = !DILocation(line: 196, column: 16, scope: !1053)
!1068 = !DILocation(line: 196, column: 26, scope: !1053)
!1069 = !DILocation(line: 196, column: 5, scope: !1053)
!1070 = !DILocation(line: 197, column: 1, scope: !1053)
!1071 = distinct !DISubprogram(name: "list_initialize", scope: !91, file: !91, line: 42, type: !1072, scopeLine: 43, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1074)
!1072 = !DISubroutineType(types: !1073)
!1073 = !{null, !94}
!1074 = !{!1075}
!1075 = !DILocalVariable(name: "list", arg: 1, scope: !1071, file: !91, line: 42, type: !94)
!1076 = !DILocation(line: 42, column: 54, scope: !1071)
!1077 = !DILocation(line: 44, column: 31, scope: !1071)
!1078 = !DILocation(line: 44, column: 18, scope: !1071)
!1079 = !DILocation(line: 44, column: 24, scope: !1071)
!1080 = !DILocation(line: 44, column: 29, scope: !1071)
!1081 = !{!447, !376, i64 4}
!1082 = !DILocation(line: 44, column: 5, scope: !1071)
!1083 = !DILocation(line: 44, column: 11, scope: !1071)
!1084 = !DILocation(line: 44, column: 16, scope: !1071)
!1085 = !{!447, !376, i64 0}
!1086 = !DILocation(line: 45, column: 1, scope: !1071)
!1087 = distinct !DISubprogram(name: "to_port_context", scope: !154, file: !154, line: 76, type: !1088, scopeLine: 76, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1090)
!1088 = !DISubroutineType(types: !1089)
!1089 = !{!117, !67}
!1090 = !{!1091}
!1091 = !DILocalVariable(name: "context", arg: 1, scope: !1087, file: !154, line: 76, type: !67)
!1092 = !DILocation(line: 76, column: 69, scope: !1087)
!1093 = !DILocation(line: 77, column: 5, scope: !1087)
!1094 = !DILocation(line: 78, column: 12, scope: !1087)
!1095 = !DILocation(line: 78, column: 5, scope: !1087)
!1096 = distinct !DISubprogram(name: "handle_port_errors", scope: !154, file: !154, line: 49, type: !873, scopeLine: 49, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1097)
!1097 = !{!1098}
!1098 = !DILocalVariable(name: "ev", arg: 1, scope: !1096, file: !154, line: 49, type: !875)
!1099 = !DILocation(line: 49, column: 55, scope: !1096)
!1100 = !DILocation(line: 50, column: 10, scope: !1101)
!1101 = distinct !DILexicalBlock(scope: !1096, file: !154, line: 50, column: 9)
!1102 = !DILocation(line: 50, column: 14, scope: !1101)
!1103 = !DILocation(line: 50, column: 20, scope: !1101)
!1104 = !DILocation(line: 50, column: 45, scope: !1101)
!1105 = !DILocation(line: 51, column: 10, scope: !1101)
!1106 = !DILocation(line: 51, column: 14, scope: !1101)
!1107 = !DILocation(line: 51, column: 20, scope: !1101)
!1108 = !DILocation(line: 51, column: 43, scope: !1101)
!1109 = !DILocation(line: 52, column: 10, scope: !1101)
!1110 = !DILocation(line: 52, column: 14, scope: !1101)
!1111 = !DILocation(line: 52, column: 20, scope: !1101)
!1112 = !DILocation(line: 52, column: 43, scope: !1101)
!1113 = !DILocation(line: 53, column: 10, scope: !1101)
!1114 = !DILocation(line: 53, column: 14, scope: !1101)
!1115 = !DILocation(line: 53, column: 20, scope: !1101)
!1116 = !DILocation(line: 50, column: 9, scope: !1096)
!1117 = !DILocation(line: 55, column: 9, scope: !1118)
!1118 = distinct !DILexicalBlock(scope: !1101, file: !154, line: 53, column: 55)
!1119 = !DILocation(line: 55, column: 9, scope: !1120)
!1120 = distinct !DILexicalBlock(scope: !1121, file: !154, line: 55, column: 9)
!1121 = distinct !DILexicalBlock(scope: !1122, file: !154, line: 55, column: 9)
!1122 = distinct !DILexicalBlock(scope: !1118, file: !154, line: 55, column: 9)
!1123 = !DILocation(line: 55, column: 9, scope: !1124)
!1124 = distinct !DILexicalBlock(scope: !1120, file: !154, line: 55, column: 9)
!1125 = !DILocation(line: 55, column: 9, scope: !1122)
!1126 = !DILocation(line: 56, column: 9, scope: !1118)
!1127 = !DILocation(line: 58, column: 1, scope: !1096)
!1128 = distinct !DISubprogram(name: "do_connect", scope: !154, file: !154, line: 87, type: !1129, scopeLine: 87, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1131)
!1129 = !DISubroutineType(types: !1130)
!1130 = !{!19, !117, !875}
!1131 = !{!1132, !1133, !1134, !1135, !1136, !1137, !1140, !1141}
!1132 = !DILocalVariable(name: "ctx", arg: 1, scope: !1128, file: !154, line: 87, type: !117)
!1133 = !DILocalVariable(name: "ev", arg: 2, scope: !1128, file: !154, line: 87, type: !875)
!1134 = !DILocalVariable(name: "rc", scope: !1128, file: !154, line: 88, type: !19)
!1135 = !DILocalVariable(name: "chan_handle", scope: !1128, file: !154, line: 89, type: !37)
!1136 = !DILocalVariable(name: "chan_ctx", scope: !1128, file: !154, line: 90, type: !55)
!1137 = !DILocalVariable(name: "peer_uuid", scope: !1138, file: !154, line: 94, type: !131)
!1138 = distinct !DILexicalBlock(scope: !1139, file: !154, line: 92, column: 44)
!1139 = distinct !DILexicalBlock(scope: !1128, file: !154, line: 92, column: 9)
!1140 = !DILabel(scope: !1128, name: "err_set_cookie", file: !154, line: 126)
!1141 = !DILabel(scope: !1128, name: "err_on_connect", file: !154, line: 128)
!1142 = !DILocation(line: 87, column: 48, scope: !1128)
!1143 = !DILocation(line: 87, column: 69, scope: !1128)
!1144 = !DILocation(line: 88, column: 5, scope: !1128)
!1145 = !DILocation(line: 88, column: 9, scope: !1128)
!1146 = !DILocation(line: 89, column: 5, scope: !1128)
!1147 = !DILocation(line: 89, column: 14, scope: !1128)
!1148 = !DILocation(line: 90, column: 5, scope: !1128)
!1149 = !DILocation(line: 90, column: 33, scope: !1128)
!1150 = !DILocation(line: 92, column: 9, scope: !1139)
!1151 = !DILocation(line: 92, column: 13, scope: !1139)
!1152 = !DILocation(line: 92, column: 19, scope: !1139)
!1153 = !DILocation(line: 92, column: 9, scope: !1128)
!1154 = !DILocation(line: 94, column: 9, scope: !1138)
!1155 = !DILocation(line: 94, column: 16, scope: !1138)
!1156 = !DILocation(line: 95, column: 21, scope: !1138)
!1157 = !DILocation(line: 95, column: 25, scope: !1138)
!1158 = !DILocation(line: 95, column: 14, scope: !1138)
!1159 = !DILocation(line: 95, column: 12, scope: !1138)
!1160 = !DILocation(line: 96, column: 13, scope: !1161)
!1161 = distinct !DILexicalBlock(scope: !1138, file: !154, line: 96, column: 13)
!1162 = !DILocation(line: 96, column: 16, scope: !1161)
!1163 = !DILocation(line: 96, column: 13, scope: !1138)
!1164 = !DILocation(line: 97, column: 13, scope: !1165)
!1165 = distinct !DILexicalBlock(scope: !1161, file: !154, line: 96, column: 21)
!1166 = !DILocation(line: 97, column: 13, scope: !1167)
!1167 = distinct !DILexicalBlock(scope: !1168, file: !154, line: 97, column: 13)
!1168 = distinct !DILexicalBlock(scope: !1169, file: !154, line: 97, column: 13)
!1169 = distinct !DILexicalBlock(scope: !1165, file: !154, line: 97, column: 13)
!1170 = !DILocation(line: 97, column: 13, scope: !1171)
!1171 = distinct !DILexicalBlock(scope: !1167, file: !154, line: 97, column: 13)
!1172 = !DILocation(line: 97, column: 13, scope: !1169)
!1173 = !DILocation(line: 98, column: 20, scope: !1165)
!1174 = !DILocation(line: 98, column: 13, scope: !1165)
!1175 = !DILocation(line: 101, column: 33, scope: !1138)
!1176 = !DILocation(line: 101, column: 21, scope: !1138)
!1177 = !DILocation(line: 103, column: 20, scope: !1138)
!1178 = !DILocation(line: 103, column: 25, scope: !1138)
!1179 = !DILocation(line: 103, column: 29, scope: !1138)
!1180 = !{!990, !376, i64 8}
!1181 = !DILocation(line: 103, column: 40, scope: !1138)
!1182 = !DILocation(line: 103, column: 57, scope: !1138)
!1183 = !DILocation(line: 103, column: 18, scope: !1138)
!1184 = !DILocation(line: 104, column: 13, scope: !1185)
!1185 = distinct !DILexicalBlock(scope: !1138, file: !154, line: 104, column: 13)
!1186 = !DILocation(line: 104, column: 22, scope: !1185)
!1187 = !DILocation(line: 104, column: 13, scope: !1138)
!1188 = !DILocation(line: 105, column: 13, scope: !1189)
!1189 = distinct !DILexicalBlock(scope: !1185, file: !154, line: 104, column: 31)
!1190 = !DILocation(line: 105, column: 13, scope: !1191)
!1191 = distinct !DILexicalBlock(scope: !1192, file: !154, line: 105, column: 13)
!1192 = distinct !DILexicalBlock(scope: !1193, file: !154, line: 105, column: 13)
!1193 = distinct !DILexicalBlock(scope: !1189, file: !154, line: 105, column: 13)
!1194 = !DILocation(line: 105, column: 13, scope: !1195)
!1195 = distinct !DILexicalBlock(scope: !1191, file: !154, line: 105, column: 13)
!1196 = !DILocation(line: 105, column: 13, scope: !1193)
!1197 = !DILocation(line: 107, column: 16, scope: !1189)
!1198 = !DILocation(line: 108, column: 13, scope: !1189)
!1199 = !DILocation(line: 111, column: 9, scope: !1138)
!1200 = !DILocation(line: 113, column: 9, scope: !1138)
!1201 = !DILocation(line: 113, column: 19, scope: !1138)
!1202 = !DILocation(line: 113, column: 26, scope: !1138)
!1203 = !DILocation(line: 113, column: 38, scope: !1138)
!1204 = !{!444, !376, i64 0}
!1205 = !DILocation(line: 114, column: 35, scope: !1138)
!1206 = !DILocation(line: 114, column: 9, scope: !1138)
!1207 = !DILocation(line: 114, column: 19, scope: !1138)
!1208 = !DILocation(line: 114, column: 26, scope: !1138)
!1209 = !DILocation(line: 114, column: 33, scope: !1138)
!1210 = !DILocation(line: 116, column: 25, scope: !1138)
!1211 = !DILocation(line: 116, column: 38, scope: !1138)
!1212 = !DILocation(line: 116, column: 14, scope: !1138)
!1213 = !DILocation(line: 116, column: 12, scope: !1138)
!1214 = !DILocation(line: 117, column: 13, scope: !1215)
!1215 = distinct !DILexicalBlock(scope: !1138, file: !154, line: 117, column: 13)
!1216 = !DILocation(line: 117, column: 16, scope: !1215)
!1217 = !DILocation(line: 117, column: 13, scope: !1138)
!1218 = !DILocation(line: 118, column: 13, scope: !1219)
!1219 = distinct !DILexicalBlock(scope: !1215, file: !154, line: 117, column: 21)
!1220 = !DILocation(line: 118, column: 13, scope: !1221)
!1221 = distinct !DILexicalBlock(scope: !1222, file: !154, line: 118, column: 13)
!1222 = distinct !DILexicalBlock(scope: !1223, file: !154, line: 118, column: 13)
!1223 = distinct !DILexicalBlock(scope: !1219, file: !154, line: 118, column: 13)
!1224 = !DILocation(line: 118, column: 13, scope: !1225)
!1225 = distinct !DILexicalBlock(scope: !1221, file: !154, line: 118, column: 13)
!1226 = !DILocation(line: 118, column: 13, scope: !1223)
!1227 = !DILocation(line: 119, column: 13, scope: !1219)
!1228 = !DILocation(line: 121, column: 24, scope: !1138)
!1229 = !DILocation(line: 121, column: 29, scope: !1138)
!1230 = !DILocation(line: 121, column: 40, scope: !1138)
!1231 = !DILocation(line: 121, column: 50, scope: !1138)
!1232 = !DILocation(line: 121, column: 9, scope: !1138)
!1233 = !DILocation(line: 122, column: 5, scope: !1139)
!1234 = !DILocation(line: 122, column: 5, scope: !1138)
!1235 = !DILocation(line: 124, column: 5, scope: !1128)
!1236 = !DILocation(line: 126, column: 1, scope: !1128)
!1237 = !DILocation(line: 127, column: 5, scope: !1128)
!1238 = !DILocation(line: 127, column: 15, scope: !1128)
!1239 = !DILocation(line: 127, column: 19, scope: !1128)
!1240 = !DILocation(line: 127, column: 33, scope: !1128)
!1241 = !DILocation(line: 128, column: 1, scope: !1128)
!1242 = !DILocation(line: 129, column: 11, scope: !1128)
!1243 = !DILocation(line: 129, column: 5, scope: !1128)
!1244 = !DILocation(line: 130, column: 12, scope: !1128)
!1245 = !DILocation(line: 130, column: 5, scope: !1128)
!1246 = !DILocation(line: 131, column: 1, scope: !1128)
!1247 = distinct !DISubprogram(name: "is_valid_chan_ops", scope: !154, file: !154, line: 72, type: !1248, scopeLine: 72, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1251)
!1248 = !DISubroutineType(types: !1249)
!1249 = !{!178, !1250}
!1250 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !77, size: 32)
!1251 = !{!1252}
!1252 = !DILocalVariable(name: "ops", arg: 1, scope: !1247, file: !154, line: 72, type: !1250)
!1253 = !DILocation(line: 72, column: 55, scope: !1247)
!1254 = !DILocation(line: 73, column: 13, scope: !1247)
!1255 = !DILocation(line: 73, column: 18, scope: !1247)
!1256 = !{!446, !376, i64 4}
!1257 = !DILocation(line: 73, column: 32, scope: !1247)
!1258 = !DILocation(line: 73, column: 5, scope: !1247)
!1259 = distinct !DISubprogram(name: "handle_channel", scope: !154, file: !154, line: 199, type: !65, scopeLine: 199, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1260)
!1260 = !{!1261, !1262, !1263, !1264}
!1261 = !DILocalVariable(name: "ctx", arg: 1, scope: !1259, file: !154, line: 199, type: !67)
!1262 = !DILocalVariable(name: "ev", arg: 2, scope: !1259, file: !154, line: 199, type: !68)
!1263 = !DILocalVariable(name: "channel_ctx", scope: !1259, file: !154, line: 200, type: !55)
!1264 = !DILocalVariable(name: "rc", scope: !1265, file: !154, line: 207, type: !19)
!1265 = distinct !DILexicalBlock(scope: !1266, file: !154, line: 206, column: 53)
!1266 = distinct !DILexicalBlock(scope: !1267, file: !154, line: 206, column: 13)
!1267 = distinct !DILexicalBlock(scope: !1268, file: !154, line: 205, column: 42)
!1268 = distinct !DILexicalBlock(scope: !1259, file: !154, line: 205, column: 9)
!1269 = !DILocation(line: 199, column: 48, scope: !1259)
!1270 = !DILocation(line: 199, column: 74, scope: !1259)
!1271 = !DILocation(line: 200, column: 5, scope: !1259)
!1272 = !DILocation(line: 200, column: 33, scope: !1259)
!1273 = !DILocation(line: 200, column: 66, scope: !1259)
!1274 = !DILocation(line: 200, column: 47, scope: !1259)
!1275 = !DILocation(line: 201, column: 5, scope: !1259)
!1276 = !DILocation(line: 203, column: 24, scope: !1259)
!1277 = !DILocation(line: 203, column: 5, scope: !1259)
!1278 = !DILocation(line: 205, column: 9, scope: !1268)
!1279 = !DILocation(line: 205, column: 13, scope: !1268)
!1280 = !DILocation(line: 205, column: 19, scope: !1268)
!1281 = !DILocation(line: 205, column: 9, scope: !1259)
!1282 = !DILocation(line: 206, column: 13, scope: !1266)
!1283 = !DILocation(line: 206, column: 26, scope: !1266)
!1284 = !DILocation(line: 206, column: 30, scope: !1266)
!1285 = !DILocation(line: 206, column: 44, scope: !1266)
!1286 = !DILocation(line: 206, column: 13, scope: !1267)
!1287 = !DILocation(line: 207, column: 13, scope: !1265)
!1288 = !DILocation(line: 207, column: 17, scope: !1265)
!1289 = !DILocation(line: 207, column: 36, scope: !1265)
!1290 = !DILocation(line: 207, column: 49, scope: !1265)
!1291 = !DILocation(line: 207, column: 22, scope: !1265)
!1292 = !DILocation(line: 208, column: 17, scope: !1293)
!1293 = distinct !DILexicalBlock(scope: !1265, file: !154, line: 208, column: 17)
!1294 = !DILocation(line: 208, column: 20, scope: !1293)
!1295 = !DILocation(line: 208, column: 17, scope: !1265)
!1296 = !DILocation(line: 209, column: 17, scope: !1297)
!1297 = distinct !DILexicalBlock(scope: !1293, file: !154, line: 208, column: 25)
!1298 = !DILocation(line: 209, column: 17, scope: !1299)
!1299 = distinct !DILexicalBlock(scope: !1300, file: !154, line: 209, column: 17)
!1300 = distinct !DILexicalBlock(scope: !1301, file: !154, line: 209, column: 17)
!1301 = distinct !DILexicalBlock(scope: !1297, file: !154, line: 209, column: 17)
!1302 = !DILocation(line: 209, column: 17, scope: !1303)
!1303 = distinct !DILexicalBlock(scope: !1299, file: !154, line: 209, column: 17)
!1304 = !DILocation(line: 209, column: 17, scope: !1301)
!1305 = !DILocation(line: 212, column: 31, scope: !1297)
!1306 = !DILocation(line: 212, column: 44, scope: !1297)
!1307 = !DILocation(line: 212, column: 17, scope: !1297)
!1308 = !DILocation(line: 213, column: 17, scope: !1297)
!1309 = !DILocation(line: 215, column: 9, scope: !1266)
!1310 = !DILocation(line: 215, column: 9, scope: !1265)
!1311 = !DILocation(line: 216, column: 13, scope: !1312)
!1312 = distinct !DILexicalBlock(scope: !1266, file: !154, line: 215, column: 16)
!1313 = !DILocation(line: 216, column: 13, scope: !1314)
!1314 = distinct !DILexicalBlock(scope: !1315, file: !154, line: 216, column: 13)
!1315 = distinct !DILexicalBlock(scope: !1316, file: !154, line: 216, column: 13)
!1316 = distinct !DILexicalBlock(scope: !1312, file: !154, line: 216, column: 13)
!1317 = !DILocation(line: 216, column: 13, scope: !1318)
!1318 = distinct !DILexicalBlock(scope: !1314, file: !154, line: 216, column: 13)
!1319 = !DILocation(line: 216, column: 13, scope: !1316)
!1320 = !DILocation(line: 218, column: 27, scope: !1312)
!1321 = !DILocation(line: 218, column: 40, scope: !1312)
!1322 = !DILocation(line: 218, column: 13, scope: !1312)
!1323 = !DILocation(line: 219, column: 13, scope: !1312)
!1324 = !DILocation(line: 221, column: 5, scope: !1267)
!1325 = !DILocation(line: 223, column: 9, scope: !1326)
!1326 = distinct !DILexicalBlock(scope: !1259, file: !154, line: 223, column: 9)
!1327 = !DILocation(line: 223, column: 13, scope: !1326)
!1328 = !DILocation(line: 223, column: 19, scope: !1326)
!1329 = !DILocation(line: 223, column: 9, scope: !1259)
!1330 = !DILocation(line: 224, column: 23, scope: !1331)
!1331 = distinct !DILexicalBlock(scope: !1326, file: !154, line: 223, column: 42)
!1332 = !DILocation(line: 224, column: 36, scope: !1331)
!1333 = !DILocation(line: 224, column: 9, scope: !1331)
!1334 = !DILocation(line: 225, column: 5, scope: !1331)
!1335 = !DILocation(line: 226, column: 1, scope: !1259)
!1336 = distinct !DISubprogram(name: "list_add_tail", scope: !91, file: !91, line: 70, type: !1337, scopeLine: 71, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1339)
!1337 = !DISubroutineType(types: !1338)
!1338 = !{null, !94, !94}
!1339 = !{!1340, !1341}
!1340 = !DILocalVariable(name: "list", arg: 1, scope: !1336, file: !91, line: 70, type: !94)
!1341 = !DILocalVariable(name: "item", arg: 2, scope: !1336, file: !91, line: 70, type: !94)
!1342 = !DILocation(line: 70, column: 52, scope: !1336)
!1343 = !DILocation(line: 70, column: 76, scope: !1336)
!1344 = !DILocation(line: 72, column: 18, scope: !1336)
!1345 = !DILocation(line: 72, column: 24, scope: !1336)
!1346 = !DILocation(line: 72, column: 5, scope: !1336)
!1347 = !DILocation(line: 72, column: 11, scope: !1336)
!1348 = !DILocation(line: 72, column: 16, scope: !1336)
!1349 = !DILocation(line: 73, column: 18, scope: !1336)
!1350 = !DILocation(line: 73, column: 5, scope: !1336)
!1351 = !DILocation(line: 73, column: 11, scope: !1336)
!1352 = !DILocation(line: 73, column: 16, scope: !1336)
!1353 = !DILocation(line: 74, column: 24, scope: !1336)
!1354 = !DILocation(line: 74, column: 5, scope: !1336)
!1355 = !DILocation(line: 74, column: 11, scope: !1336)
!1356 = !DILocation(line: 74, column: 17, scope: !1336)
!1357 = !DILocation(line: 74, column: 22, scope: !1336)
!1358 = !DILocation(line: 75, column: 18, scope: !1336)
!1359 = !DILocation(line: 75, column: 5, scope: !1336)
!1360 = !DILocation(line: 75, column: 11, scope: !1336)
!1361 = !DILocation(line: 75, column: 16, scope: !1336)
!1362 = !DILocation(line: 76, column: 1, scope: !1336)
!1363 = distinct !DISubprogram(name: "to_channel_context", scope: !154, file: !154, line: 81, type: !1364, scopeLine: 82, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1366)
!1364 = !DISubroutineType(types: !1365)
!1365 = !{!55, !67}
!1366 = !{!1367}
!1367 = !DILocalVariable(name: "context", arg: 1, scope: !1363, file: !154, line: 82, type: !67)
!1368 = !DILocation(line: 82, column: 29, scope: !1363)
!1369 = !DILocation(line: 83, column: 5, scope: !1363)
!1370 = !DILocation(line: 84, column: 12, scope: !1363)
!1371 = !DILocation(line: 84, column: 5, scope: !1363)
!1372 = distinct !DISubprogram(name: "handle_chan_errors", scope: !154, file: !154, line: 60, type: !873, scopeLine: 60, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1373)
!1373 = !{!1374}
!1374 = !DILocalVariable(name: "ev", arg: 1, scope: !1372, file: !154, line: 60, type: !875)
!1375 = !DILocation(line: 60, column: 55, scope: !1372)
!1376 = !DILocation(line: 61, column: 10, scope: !1377)
!1377 = distinct !DILexicalBlock(scope: !1372, file: !154, line: 61, column: 9)
!1378 = !DILocation(line: 61, column: 14, scope: !1377)
!1379 = !DILocation(line: 61, column: 20, scope: !1377)
!1380 = !DILocation(line: 61, column: 45, scope: !1377)
!1381 = !DILocation(line: 62, column: 10, scope: !1377)
!1382 = !DILocation(line: 62, column: 14, scope: !1377)
!1383 = !DILocation(line: 62, column: 20, scope: !1377)
!1384 = !DILocation(line: 61, column: 9, scope: !1372)
!1385 = !DILocation(line: 63, column: 9, scope: !1386)
!1386 = distinct !DILexicalBlock(scope: !1377, file: !154, line: 62, column: 46)
!1387 = !DILocation(line: 63, column: 9, scope: !1388)
!1388 = distinct !DILexicalBlock(scope: !1389, file: !154, line: 63, column: 9)
!1389 = distinct !DILexicalBlock(scope: !1390, file: !154, line: 63, column: 9)
!1390 = distinct !DILexicalBlock(scope: !1386, file: !154, line: 63, column: 9)
!1391 = !DILocation(line: 63, column: 9, scope: !1392)
!1392 = distinct !DILexicalBlock(scope: !1388, file: !154, line: 63, column: 9)
!1393 = !DILocation(line: 63, column: 9, scope: !1390)
!1394 = !DILocation(line: 64, column: 9, scope: !1386)
!1395 = !DILocation(line: 66, column: 1, scope: !1372)
!1396 = distinct !DISubprogram(name: "do_handle_msg", scope: !154, file: !154, line: 133, type: !1397, scopeLine: 133, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1399)
!1397 = !DISubroutineType(types: !1398)
!1398 = !{!19, !55, !875}
!1399 = !{!1400, !1401, !1402, !1403, !1405, !1406, !1407, !1409, !1410}
!1400 = !DILocalVariable(name: "ctx", arg: 1, scope: !1396, file: !154, line: 133, type: !55)
!1401 = !DILocalVariable(name: "ev", arg: 2, scope: !1396, file: !154, line: 133, type: !875)
!1402 = !DILocalVariable(name: "chan", scope: !1396, file: !154, line: 134, type: !37)
!1403 = !DILocalVariable(name: "msg_inf", scope: !1396, file: !154, line: 137, type: !1404)
!1404 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_msg_info_t", file: !6, line: 84, baseType: !109)
!1405 = !DILocalVariable(name: "rc", scope: !1396, file: !154, line: 138, type: !19)
!1406 = !DILocalVariable(name: "iov", scope: !1396, file: !154, line: 155, type: !28)
!1407 = !DILocalVariable(name: "msg", scope: !1396, file: !154, line: 159, type: !1408)
!1408 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_msg_t", file: !6, line: 78, baseType: !21)
!1409 = !DILabel(scope: !1396, name: "err_handle_msg", file: !154, line: 178)
!1410 = !DILabel(scope: !1396, name: "err_read_msg", file: !154, line: 179)
!1411 = !DILocation(line: 133, column: 54, scope: !1396)
!1412 = !DILocation(line: 133, column: 75, scope: !1396)
!1413 = !DILocation(line: 134, column: 5, scope: !1396)
!1414 = !DILocation(line: 134, column: 14, scope: !1396)
!1415 = !DILocation(line: 134, column: 21, scope: !1396)
!1416 = !DILocation(line: 134, column: 25, scope: !1396)
!1417 = !DILocation(line: 137, column: 5, scope: !1396)
!1418 = !DILocation(line: 137, column: 20, scope: !1396)
!1419 = !DILocation(line: 138, column: 5, scope: !1396)
!1420 = !DILocation(line: 138, column: 9, scope: !1396)
!1421 = !DILocation(line: 138, column: 22, scope: !1396)
!1422 = !DILocation(line: 138, column: 14, scope: !1396)
!1423 = !DILocation(line: 139, column: 9, scope: !1424)
!1424 = distinct !DILexicalBlock(scope: !1396, file: !154, line: 139, column: 9)
!1425 = !DILocation(line: 139, column: 12, scope: !1424)
!1426 = !DILocation(line: 139, column: 9, scope: !1396)
!1427 = !DILocation(line: 140, column: 9, scope: !1424)
!1428 = !DILocation(line: 142, column: 9, scope: !1429)
!1429 = distinct !DILexicalBlock(scope: !1396, file: !154, line: 142, column: 9)
!1430 = !DILocation(line: 142, column: 12, scope: !1429)
!1431 = !DILocation(line: 142, column: 9, scope: !1396)
!1432 = !DILocation(line: 143, column: 9, scope: !1433)
!1433 = distinct !DILexicalBlock(scope: !1429, file: !154, line: 142, column: 25)
!1434 = !DILocation(line: 143, column: 9, scope: !1435)
!1435 = distinct !DILexicalBlock(scope: !1436, file: !154, line: 143, column: 9)
!1436 = distinct !DILexicalBlock(scope: !1437, file: !154, line: 143, column: 9)
!1437 = distinct !DILexicalBlock(scope: !1433, file: !154, line: 143, column: 9)
!1438 = !DILocation(line: 143, column: 9, scope: !1439)
!1439 = distinct !DILexicalBlock(scope: !1435, file: !154, line: 143, column: 9)
!1440 = !DILocation(line: 143, column: 9, scope: !1437)
!1441 = !DILocation(line: 145, column: 16, scope: !1433)
!1442 = !DILocation(line: 145, column: 9, scope: !1433)
!1443 = !DILocation(line: 148, column: 17, scope: !1444)
!1444 = distinct !DILexicalBlock(scope: !1396, file: !154, line: 148, column: 9)
!1445 = !DILocation(line: 148, column: 21, scope: !1444)
!1446 = !DILocation(line: 148, column: 9, scope: !1396)
!1447 = !DILocation(line: 149, column: 9, scope: !1448)
!1448 = distinct !DILexicalBlock(scope: !1444, file: !154, line: 148, column: 41)
!1449 = !DILocation(line: 149, column: 9, scope: !1450)
!1450 = distinct !DILexicalBlock(scope: !1451, file: !154, line: 149, column: 9)
!1451 = distinct !DILexicalBlock(scope: !1452, file: !154, line: 149, column: 9)
!1452 = distinct !DILexicalBlock(scope: !1448, file: !154, line: 149, column: 9)
!1453 = !DILocation(line: 149, column: 9, scope: !1454)
!1454 = distinct !DILexicalBlock(scope: !1450, file: !154, line: 149, column: 9)
!1455 = !DILocation(line: 149, column: 9, scope: !1452)
!1456 = !DILocation(line: 150, column: 17, scope: !1448)
!1457 = !DILocation(line: 150, column: 31, scope: !1448)
!1458 = !DILocation(line: 150, column: 9, scope: !1448)
!1459 = !DILocation(line: 151, column: 9, scope: !1448)
!1460 = !DILocation(line: 155, column: 5, scope: !1396)
!1461 = !DILocation(line: 155, column: 18, scope: !1396)
!1462 = !DILocation(line: 155, column: 24, scope: !1396)
!1463 = !DILocation(line: 156, column: 25, scope: !1396)
!1464 = !DILocation(line: 157, column: 32, scope: !1396)
!1465 = !DILocation(line: 159, column: 5, scope: !1396)
!1466 = !DILocation(line: 159, column: 15, scope: !1396)
!1467 = !DILocation(line: 159, column: 21, scope: !1396)
!1468 = !DILocation(line: 164, column: 19, scope: !1396)
!1469 = !DILocation(line: 164, column: 33, scope: !1396)
!1470 = !DILocation(line: 164, column: 10, scope: !1396)
!1471 = !DILocation(line: 164, column: 8, scope: !1396)
!1472 = !DILocation(line: 165, column: 13, scope: !1396)
!1473 = !DILocation(line: 165, column: 27, scope: !1396)
!1474 = !DILocation(line: 165, column: 5, scope: !1396)
!1475 = !DILocation(line: 166, column: 9, scope: !1476)
!1476 = distinct !DILexicalBlock(scope: !1396, file: !154, line: 166, column: 9)
!1477 = !DILocation(line: 166, column: 12, scope: !1476)
!1478 = !DILocation(line: 166, column: 9, scope: !1396)
!1479 = !DILocation(line: 167, column: 9, scope: !1480)
!1480 = distinct !DILexicalBlock(scope: !1476, file: !154, line: 166, column: 17)
!1481 = !DILocation(line: 167, column: 9, scope: !1482)
!1482 = distinct !DILexicalBlock(scope: !1483, file: !154, line: 167, column: 9)
!1483 = distinct !DILexicalBlock(scope: !1484, file: !154, line: 167, column: 9)
!1484 = distinct !DILexicalBlock(scope: !1480, file: !154, line: 167, column: 9)
!1485 = !DILocation(line: 167, column: 9, scope: !1486)
!1486 = distinct !DILexicalBlock(scope: !1482, file: !154, line: 167, column: 9)
!1487 = !DILocation(line: 167, column: 9, scope: !1484)
!1488 = !DILocation(line: 168, column: 16, scope: !1480)
!1489 = !DILocation(line: 168, column: 9, scope: !1480)
!1490 = !DILocation(line: 171, column: 18, scope: !1491)
!1491 = distinct !DILexicalBlock(scope: !1396, file: !154, line: 171, column: 9)
!1492 = !DILocation(line: 171, column: 32, scope: !1491)
!1493 = !DILocation(line: 171, column: 22, scope: !1491)
!1494 = !DILocation(line: 171, column: 9, scope: !1396)
!1495 = !DILocation(line: 172, column: 9, scope: !1496)
!1496 = distinct !DILexicalBlock(scope: !1491, file: !154, line: 171, column: 37)
!1497 = !DILocation(line: 172, column: 9, scope: !1498)
!1498 = distinct !DILexicalBlock(scope: !1499, file: !154, line: 172, column: 9)
!1499 = distinct !DILexicalBlock(scope: !1500, file: !154, line: 172, column: 9)
!1500 = distinct !DILexicalBlock(scope: !1496, file: !154, line: 172, column: 9)
!1501 = !DILocation(line: 172, column: 9, scope: !1502)
!1502 = distinct !DILexicalBlock(scope: !1498, file: !154, line: 172, column: 9)
!1503 = !DILocation(line: 172, column: 9, scope: !1500)
!1504 = !DILocation(line: 173, column: 9, scope: !1496)
!1505 = !DILocation(line: 176, column: 10, scope: !1396)
!1506 = !DILocation(line: 176, column: 15, scope: !1396)
!1507 = !DILocation(line: 176, column: 19, scope: !1396)
!1508 = !DILocation(line: 176, column: 33, scope: !1396)
!1509 = !DILocation(line: 176, column: 38, scope: !1396)
!1510 = !DILocation(line: 176, column: 55, scope: !1396)
!1511 = !DILocation(line: 176, column: 8, scope: !1396)
!1512 = !DILocation(line: 176, column: 5, scope: !1396)
!1513 = !DILocation(line: 178, column: 1, scope: !1396)
!1514 = !DILocation(line: 179, column: 1, scope: !1396)
!1515 = !DILocation(line: 180, column: 12, scope: !1396)
!1516 = !DILocation(line: 180, column: 5, scope: !1396)
!1517 = !DILocation(line: 181, column: 1, scope: !1396)
!1518 = distinct !DISubprogram(name: "do_disconnect", scope: !154, file: !154, line: 183, type: !1519, scopeLine: 184, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1521)
!1519 = !DISubroutineType(types: !1520)
!1520 = !{null, !55, !875}
!1521 = !{!1522, !1523}
!1522 = !DILocalVariable(name: "context", arg: 1, scope: !1518, file: !154, line: 183, type: !55)
!1523 = !DILocalVariable(name: "ev", arg: 2, scope: !1518, file: !154, line: 184, type: !875)
!1524 = !DILocation(line: 183, column: 55, scope: !1518)
!1525 = !DILocation(line: 184, column: 43, scope: !1518)
!1526 = !DILocation(line: 185, column: 18, scope: !1518)
!1527 = !DILocation(line: 185, column: 27, scope: !1518)
!1528 = !DILocation(line: 185, column: 5, scope: !1518)
!1529 = !DILocation(line: 186, column: 5, scope: !1518)
!1530 = !DILocation(line: 186, column: 14, scope: !1518)
!1531 = !DILocation(line: 186, column: 18, scope: !1518)
!1532 = !DILocation(line: 186, column: 32, scope: !1518)
!1533 = !DILocation(line: 187, column: 11, scope: !1518)
!1534 = !DILocation(line: 187, column: 15, scope: !1518)
!1535 = !DILocation(line: 187, column: 5, scope: !1518)
!1536 = !DILocation(line: 188, column: 1, scope: !1518)
!1537 = distinct !DISubprogram(name: "list_delete", scope: !91, file: !91, line: 80, type: !1072, scopeLine: 81, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1538)
!1538 = !{!1539}
!1539 = !DILocalVariable(name: "item", arg: 1, scope: !1537, file: !91, line: 80, type: !94)
!1540 = !DILocation(line: 80, column: 50, scope: !1537)
!1541 = !DILocation(line: 82, column: 24, scope: !1537)
!1542 = !DILocation(line: 82, column: 30, scope: !1537)
!1543 = !DILocation(line: 82, column: 5, scope: !1537)
!1544 = !DILocation(line: 82, column: 11, scope: !1537)
!1545 = !DILocation(line: 82, column: 17, scope: !1537)
!1546 = !DILocation(line: 82, column: 22, scope: !1537)
!1547 = !DILocation(line: 83, column: 24, scope: !1537)
!1548 = !DILocation(line: 83, column: 30, scope: !1537)
!1549 = !DILocation(line: 83, column: 5, scope: !1537)
!1550 = !DILocation(line: 83, column: 11, scope: !1537)
!1551 = !DILocation(line: 83, column: 17, scope: !1537)
!1552 = !DILocation(line: 83, column: 22, scope: !1537)
!1553 = !DILocation(line: 84, column: 18, scope: !1537)
!1554 = !DILocation(line: 84, column: 24, scope: !1537)
!1555 = !DILocation(line: 84, column: 29, scope: !1537)
!1556 = !DILocation(line: 84, column: 5, scope: !1537)
!1557 = !DILocation(line: 84, column: 11, scope: !1537)
!1558 = !DILocation(line: 84, column: 16, scope: !1537)
!1559 = !DILocation(line: 85, column: 1, scope: !1537)
!1560 = distinct !DISubprogram(name: "ipc_port_destroy", scope: !154, file: !154, line: 415, type: !1561, scopeLine: 415, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1563)
!1561 = !DISubroutineType(types: !1562)
!1562 = !{!19, !117}
!1563 = !{!1564, !1565, !1567, !1569, !1570, !1571, !1572}
!1564 = !DILocalVariable(name: "ctx", arg: 1, scope: !1560, file: !154, line: 415, type: !117)
!1565 = !DILocalVariable(name: "chan_ctx", scope: !1566, file: !154, line: 418, type: !55)
!1566 = distinct !DILexicalBlock(scope: !1560, file: !154, line: 417, column: 44)
!1567 = !DILocalVariable(name: "__ptr", scope: !1568, file: !154, line: 419, type: !94)
!1568 = distinct !DILexicalBlock(scope: !1566, file: !154, line: 419, column: 6)
!1569 = !DILocalVariable(name: "__t", scope: !1568, file: !154, line: 419, type: !55)
!1570 = !DILocalVariable(name: "chan_handle", scope: !1566, file: !154, line: 422, type: !37)
!1571 = !DILocalVariable(name: "p", scope: !1566, file: !154, line: 425, type: !97)
!1572 = !DILocalVariable(name: "x", scope: !1566, file: !154, line: 426, type: !48)
!1573 = !DILocation(line: 415, column: 47, scope: !1560)
!1574 = !DILocation(line: 416, column: 11, scope: !1560)
!1575 = !DILocation(line: 416, column: 16, scope: !1560)
!1576 = !DILocation(line: 416, column: 23, scope: !1560)
!1577 = !DILocation(line: 416, column: 5, scope: !1560)
!1578 = !DILocation(line: 417, column: 5, scope: !1560)
!1579 = !DILocation(line: 417, column: 28, scope: !1560)
!1580 = !DILocation(line: 417, column: 33, scope: !1560)
!1581 = !DILocation(line: 417, column: 13, scope: !1560)
!1582 = !DILocation(line: 417, column: 12, scope: !1560)
!1583 = !DILocation(line: 418, column: 9, scope: !1566)
!1584 = !DILocation(line: 418, column: 37, scope: !1566)
!1585 = !DILocation(line: 419, column: 6, scope: !1568)
!1586 = !DILocation(line: 419, column: 6, scope: !1587)
!1587 = distinct !DILexicalBlock(scope: !1568, file: !154, line: 419, column: 6)
!1588 = !DILocation(line: 419, column: 6, scope: !1566)
!1589 = !DILocation(line: 421, column: 9, scope: !1566)
!1590 = !DILocation(line: 422, column: 9, scope: !1566)
!1591 = !DILocation(line: 422, column: 18, scope: !1566)
!1592 = !DILocation(line: 422, column: 32, scope: !1566)
!1593 = !DILocation(line: 422, column: 42, scope: !1566)
!1594 = !DILocation(line: 422, column: 49, scope: !1566)
!1595 = !DILocation(line: 423, column: 9, scope: !1566)
!1596 = !DILocation(line: 423, column: 9, scope: !1597)
!1597 = distinct !DILexicalBlock(scope: !1598, file: !154, line: 423, column: 9)
!1598 = distinct !DILexicalBlock(scope: !1599, file: !154, line: 423, column: 9)
!1599 = distinct !DILexicalBlock(scope: !1566, file: !154, line: 423, column: 9)
!1600 = !DILocation(line: 423, column: 9, scope: !1601)
!1601 = distinct !DILexicalBlock(scope: !1597, file: !154, line: 423, column: 9)
!1602 = !DILocation(line: 423, column: 9, scope: !1599)
!1603 = !DILocation(line: 424, column: 9, scope: !1566)
!1604 = !DILocation(line: 424, column: 19, scope: !1566)
!1605 = !DILocation(line: 424, column: 23, scope: !1566)
!1606 = !DILocation(line: 424, column: 37, scope: !1566)
!1607 = !DILocation(line: 425, column: 2, scope: !1566)
!1608 = !DILocation(line: 425, column: 9, scope: !1566)
!1609 = !DILocation(line: 425, column: 22, scope: !1566)
!1610 = !DILocation(line: 425, column: 13, scope: !1566)
!1611 = !DILocation(line: 425, column: 31, scope: !1566)
!1612 = !DILocation(line: 425, column: 68, scope: !1566)
!1613 = !DILocation(line: 426, column: 2, scope: !1566)
!1614 = !DILocation(line: 426, column: 7, scope: !1566)
!1615 = !DILocation(line: 426, column: 12, scope: !1566)
!1616 = !DILocation(line: 426, column: 11, scope: !1566)
!1617 = !{!361, !361, i64 0}
!1618 = !DILocation(line: 427, column: 2, scope: !1566)
!1619 = !DILocation(line: 427, column: 2, scope: !1620)
!1620 = distinct !DILexicalBlock(scope: !1621, file: !154, line: 427, column: 2)
!1621 = distinct !DILexicalBlock(scope: !1622, file: !154, line: 427, column: 2)
!1622 = distinct !DILexicalBlock(scope: !1566, file: !154, line: 427, column: 2)
!1623 = !DILocation(line: 427, column: 2, scope: !1624)
!1624 = distinct !DILexicalBlock(scope: !1620, file: !154, line: 427, column: 2)
!1625 = !DILocation(line: 427, column: 2, scope: !1622)
!1626 = !DILocation(line: 429, column: 15, scope: !1566)
!1627 = !DILocation(line: 429, column: 9, scope: !1566)
!1628 = !DILocation(line: 430, column: 5, scope: !1560)
!1629 = distinct !{!1629, !1578, !1628}
!1630 = !DILocation(line: 431, column: 5, scope: !1560)
!1631 = distinct !DISubprogram(name: "list_is_empty", scope: !91, file: !91, line: 221, type: !1632, scopeLine: 222, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1634)
!1632 = !DISubroutineType(types: !1633)
!1633 = !{!178, !94}
!1634 = !{!1635}
!1635 = !DILocalVariable(name: "list", arg: 1, scope: !1631, file: !91, line: 221, type: !94)
!1636 = !DILocation(line: 221, column: 52, scope: !1631)
!1637 = !DILocation(line: 223, column: 13, scope: !1631)
!1638 = !DILocation(line: 223, column: 19, scope: !1631)
!1639 = !DILocation(line: 223, column: 27, scope: !1631)
!1640 = !DILocation(line: 223, column: 24, scope: !1631)
!1641 = !DILocation(line: 223, column: 12, scope: !1631)
!1642 = !DILocation(line: 223, column: 5, scope: !1631)
!1643 = distinct !DISubprogram(name: "list_remove_head", scope: !91, file: !91, line: 87, type: !1644, scopeLine: 88, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1646)
!1644 = !DISubroutineType(types: !1645)
!1645 = !{!94, !94}
!1646 = !{!1647, !1648}
!1647 = !DILocalVariable(name: "list", arg: 1, scope: !1643, file: !91, line: 87, type: !94)
!1648 = !DILocalVariable(name: "item", scope: !1649, file: !91, line: 90, type: !94)
!1649 = distinct !DILexicalBlock(scope: !1650, file: !91, line: 89, column: 29)
!1650 = distinct !DILexicalBlock(scope: !1643, file: !91, line: 89, column: 9)
!1651 = !DILocation(line: 87, column: 68, scope: !1643)
!1652 = !DILocation(line: 89, column: 9, scope: !1650)
!1653 = !DILocation(line: 89, column: 15, scope: !1650)
!1654 = !DILocation(line: 89, column: 23, scope: !1650)
!1655 = !DILocation(line: 89, column: 20, scope: !1650)
!1656 = !DILocation(line: 89, column: 9, scope: !1643)
!1657 = !DILocation(line: 90, column: 9, scope: !1649)
!1658 = !DILocation(line: 90, column: 27, scope: !1649)
!1659 = !DILocation(line: 90, column: 34, scope: !1649)
!1660 = !DILocation(line: 90, column: 40, scope: !1649)
!1661 = !DILocation(line: 91, column: 21, scope: !1649)
!1662 = !DILocation(line: 91, column: 9, scope: !1649)
!1663 = !DILocation(line: 92, column: 16, scope: !1649)
!1664 = !DILocation(line: 92, column: 9, scope: !1649)
!1665 = !DILocation(line: 93, column: 5, scope: !1650)
!1666 = !DILocation(line: 94, column: 9, scope: !1667)
!1667 = distinct !DILexicalBlock(scope: !1650, file: !91, line: 93, column: 12)
!1668 = !DILocation(line: 96, column: 1, scope: !1643)
!1669 = distinct !DISubprogram(name: "ipc_loop", scope: !154, file: !154, line: 434, type: !1670, scopeLine: 434, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !2, retainedNodes: !1672)
!1670 = !DISubroutineType(types: !1671)
!1671 = !{null}
!1672 = !{!1673, !1674}
!1673 = !DILocalVariable(name: "rc", scope: !1669, file: !154, line: 435, type: !19)
!1674 = !DILocalVariable(name: "event", scope: !1669, file: !154, line: 436, type: !777)
!1675 = !DILocation(line: 435, column: 5, scope: !1669)
!1676 = !DILocation(line: 435, column: 9, scope: !1669)
!1677 = !DILocation(line: 436, column: 5, scope: !1669)
!1678 = !DILocation(line: 436, column: 14, scope: !1669)
!1679 = !DILocation(line: 438, column: 5, scope: !1669)
!1680 = !DILocation(line: 439, column: 15, scope: !1681)
!1681 = distinct !DILexicalBlock(scope: !1669, file: !154, line: 438, column: 18)
!1682 = !DILocation(line: 439, column: 22, scope: !1681)
!1683 = !DILocation(line: 440, column: 15, scope: !1681)
!1684 = !DILocation(line: 440, column: 21, scope: !1681)
!1685 = !DILocation(line: 441, column: 15, scope: !1681)
!1686 = !DILocation(line: 441, column: 22, scope: !1681)
!1687 = !DILocation(line: 442, column: 14, scope: !1681)
!1688 = !DILocation(line: 442, column: 12, scope: !1681)
!1689 = !DILocation(line: 443, column: 13, scope: !1690)
!1690 = distinct !DILexicalBlock(scope: !1681, file: !154, line: 443, column: 13)
!1691 = !DILocation(line: 443, column: 16, scope: !1690)
!1692 = !DILocation(line: 443, column: 13, scope: !1681)
!1693 = !DILocation(line: 444, column: 13, scope: !1694)
!1694 = distinct !DILexicalBlock(scope: !1690, file: !154, line: 443, column: 21)
!1695 = !DILocation(line: 444, column: 13, scope: !1696)
!1696 = distinct !DILexicalBlock(scope: !1697, file: !154, line: 444, column: 13)
!1697 = distinct !DILexicalBlock(scope: !1698, file: !154, line: 444, column: 13)
!1698 = distinct !DILexicalBlock(scope: !1694, file: !154, line: 444, column: 13)
!1699 = !DILocation(line: 444, column: 13, scope: !1700)
!1700 = distinct !DILexicalBlock(scope: !1696, file: !154, line: 444, column: 13)
!1701 = !DILocation(line: 444, column: 13, scope: !1698)
!1702 = !DILocation(line: 445, column: 13, scope: !1694)
!1703 = !DILocation(line: 448, column: 13, scope: !1704)
!1704 = distinct !DILexicalBlock(scope: !1681, file: !154, line: 448, column: 13)
!1705 = !DILocation(line: 448, column: 16, scope: !1704)
!1706 = !DILocation(line: 448, column: 13, scope: !1681)
!1707 = !DILocation(line: 449, column: 13, scope: !1708)
!1708 = distinct !DILexicalBlock(scope: !1704, file: !154, line: 448, column: 29)
!1709 = !DILocation(line: 450, column: 9, scope: !1708)
!1710 = distinct !{!1710, !1679, !1711}
!1711 = !DILocation(line: 451, column: 5, scope: !1669)
!1712 = !DILocation(line: 452, column: 1, scope: !1669)
!1713 = distinct !DISubprogram(name: "get_msg", scope: !166, file: !166, line: 34, type: !1714, scopeLine: 34, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !1723)
!1714 = !DISubroutineType(types: !1715)
!1715 = !{!19, !37, !1716}
!1716 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1717, size: 32)
!1717 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_msg_info_t", file: !6, line: 84, baseType: !1718)
!1718 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_msg_info", file: !6, line: 80, size: 96, elements: !1719)
!1719 = !{!1720, !1721, !1722}
!1720 = !DIDerivedType(tag: DW_TAG_member, name: "len", scope: !1718, file: !6, line: 81, baseType: !33, size: 32)
!1721 = !DIDerivedType(tag: DW_TAG_member, name: "id", scope: !1718, file: !6, line: 82, baseType: !24, size: 32, offset: 32)
!1722 = !DIDerivedType(tag: DW_TAG_member, name: "num_handles", scope: !1718, file: !6, line: 83, baseType: !24, size: 32, offset: 64)
!1723 = !{!1724, !1725, !1726, !1727, !1728}
!1724 = !DILocalVariable(name: "handle", arg: 1, scope: !1713, file: !166, line: 34, type: !37)
!1725 = !DILocalVariable(name: "msg_info", arg: 2, scope: !1713, file: !166, line: 34, type: !1716)
!1726 = !DILocalVariable(name: "retval", scope: !1713, file: !166, line: 36, type: !19)
!1727 = !DILocalVariable(name: "msg_len", scope: !1713, file: !166, line: 37, type: !33)
!1728 = !DILocalVariable(name: "msg_id", scope: !1713, file: !166, line: 38, type: !24)
!1729 = !DILocation(line: 34, column: 22, scope: !1713)
!1730 = !DILocation(line: 34, column: 46, scope: !1713)
!1731 = !DILocation(line: 35, column: 9, scope: !1713)
!1732 = !DILocation(line: 36, column: 3, scope: !1713)
!1733 = !DILocation(line: 36, column: 7, scope: !1713)
!1734 = !DILocation(line: 36, column: 16, scope: !1713)
!1735 = !DILocation(line: 37, column: 3, scope: !1713)
!1736 = !DILocation(line: 37, column: 10, scope: !1713)
!1737 = !DILocation(line: 37, column: 20, scope: !1713)
!1738 = !DILocation(line: 38, column: 3, scope: !1713)
!1739 = !DILocation(line: 38, column: 12, scope: !1713)
!1740 = !DILocation(line: 38, column: 21, scope: !1713)
!1741 = !DILocation(line: 39, column: 7, scope: !1742)
!1742 = distinct !DILexicalBlock(scope: !1713, file: !166, line: 39, column: 7)
!1743 = !DILocation(line: 39, column: 14, scope: !1742)
!1744 = !DILocation(line: 39, column: 7, scope: !1713)
!1745 = !DILocation(line: 40, column: 12, scope: !1746)
!1746 = distinct !DILexicalBlock(scope: !1742, file: !166, line: 39, column: 27)
!1747 = !DILocation(line: 40, column: 20, scope: !1746)
!1748 = !DILocation(line: 40, column: 5, scope: !1746)
!1749 = !DILocation(line: 41, column: 12, scope: !1746)
!1750 = !DILocation(line: 41, column: 19, scope: !1746)
!1751 = !DILocation(line: 41, column: 5, scope: !1746)
!1752 = !DILocation(line: 42, column: 18, scope: !1746)
!1753 = !DILocation(line: 42, column: 16, scope: !1746)
!1754 = !DILocation(line: 43, column: 21, scope: !1746)
!1755 = !{!1756, !1756, i64 0}
!1756 = !{!"_Bool", !361, i64 0}
!1757 = !DILocation(line: 44, column: 3, scope: !1746)
!1758 = !DILocation(line: 45, column: 13, scope: !1759)
!1759 = distinct !DILexicalBlock(scope: !1742, file: !166, line: 44, column: 10)
!1760 = !DILocation(line: 46, column: 12, scope: !1759)
!1761 = !DILocation(line: 48, column: 19, scope: !1713)
!1762 = !DILocation(line: 48, column: 3, scope: !1713)
!1763 = !DILocation(line: 48, column: 13, scope: !1713)
!1764 = !DILocation(line: 48, column: 17, scope: !1713)
!1765 = !DILocation(line: 49, column: 18, scope: !1713)
!1766 = !DILocation(line: 49, column: 3, scope: !1713)
!1767 = !DILocation(line: 49, column: 13, scope: !1713)
!1768 = !DILocation(line: 49, column: 16, scope: !1713)
!1769 = !DILocation(line: 50, column: 10, scope: !1713)
!1770 = !DILocation(line: 51, column: 1, scope: !1713)
!1771 = !DILocation(line: 50, column: 3, scope: !1713)
!1772 = distinct !DISubprogram(name: "read_msg", scope: !166, file: !166, line: 61, type: !1773, scopeLine: 62, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !1789)
!1773 = !DISubroutineType(types: !1774)
!1774 = !{!1775, !37, !24, !24, !1776}
!1775 = !DIDerivedType(tag: DW_TAG_typedef, name: "ssize_t", file: !25, line: 103, baseType: !19)
!1776 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1777, size: 32)
!1777 = !DIDerivedType(tag: DW_TAG_typedef, name: "ipc_msg_t", file: !6, line: 78, baseType: !1778)
!1778 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "ipc_msg", file: !6, line: 72, size: 128, elements: !1779)
!1779 = !{!1780, !1781, !1787, !1788}
!1780 = !DIDerivedType(tag: DW_TAG_member, name: "num_iov", scope: !1778, file: !6, line: 73, baseType: !24, size: 32)
!1781 = !DIDerivedType(tag: DW_TAG_member, name: "iov", scope: !1778, file: !6, line: 74, baseType: !1782, size: 32, offset: 32)
!1782 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1783, size: 32)
!1783 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "iovec", file: !25, line: 372, size: 64, elements: !1784)
!1784 = !{!1785, !1786}
!1785 = !DIDerivedType(tag: DW_TAG_member, name: "iov_base", scope: !1783, file: !25, line: 372, baseType: !31, size: 32)
!1786 = !DIDerivedType(tag: DW_TAG_member, name: "iov_len", scope: !1783, file: !25, line: 372, baseType: !33, size: 32, offset: 32)
!1787 = !DIDerivedType(tag: DW_TAG_member, name: "num_handles", scope: !1778, file: !6, line: 76, baseType: !24, size: 32, offset: 64)
!1788 = !DIDerivedType(tag: DW_TAG_member, name: "handles", scope: !1778, file: !6, line: 77, baseType: !36, size: 32, offset: 96)
!1789 = !{!1790, !1791, !1792, !1793, !1794, !1795, !1796, !1797, !1801}
!1790 = !DILocalVariable(name: "handle", arg: 1, scope: !1772, file: !166, line: 61, type: !37)
!1791 = !DILocalVariable(name: "msg_id", arg: 2, scope: !1772, file: !166, line: 61, type: !24)
!1792 = !DILocalVariable(name: "offset", arg: 3, scope: !1772, file: !166, line: 61, type: !24)
!1793 = !DILocalVariable(name: "msg", arg: 4, scope: !1772, file: !166, line: 62, type: !1776)
!1794 = !DILocalVariable(name: "res", scope: !1772, file: !166, line: 69, type: !1775)
!1795 = !DILocalVariable(name: "iovecs", scope: !1772, file: !166, line: 70, type: !1782)
!1796 = !DILocalVariable(name: "iovec_cnt", scope: !1772, file: !166, line: 71, type: !33)
!1797 = !DILocalVariable(name: "i", scope: !1798, file: !166, line: 73, type: !33)
!1798 = distinct !DILexicalBlock(scope: !1799, file: !166, line: 73, column: 5)
!1799 = distinct !DILexicalBlock(scope: !1800, file: !166, line: 72, column: 17)
!1800 = distinct !DILexicalBlock(scope: !1772, file: !166, line: 72, column: 7)
!1801 = !DILocalVariable(name: "iv", scope: !1802, file: !166, line: 75, type: !1783)
!1802 = distinct !DILexicalBlock(scope: !1803, file: !166, line: 73, column: 44)
!1803 = distinct !DILexicalBlock(scope: !1798, file: !166, line: 73, column: 5)
!1804 = !DILocation(line: 61, column: 27, scope: !1772)
!1805 = !DILocation(line: 61, column: 44, scope: !1772)
!1806 = !DILocation(line: 61, column: 61, scope: !1772)
!1807 = !DILocation(line: 62, column: 29, scope: !1772)
!1808 = !DILocation(line: 67, column: 9, scope: !1772)
!1809 = !DILocation(line: 68, column: 9, scope: !1772)
!1810 = !DILocation(line: 69, column: 3, scope: !1772)
!1811 = !DILocation(line: 69, column: 11, scope: !1772)
!1812 = !DILocation(line: 69, column: 17, scope: !1772)
!1813 = !DILocation(line: 70, column: 3, scope: !1772)
!1814 = !DILocation(line: 70, column: 17, scope: !1772)
!1815 = !DILocation(line: 70, column: 26, scope: !1772)
!1816 = !DILocation(line: 70, column: 31, scope: !1772)
!1817 = !DILocation(line: 71, column: 3, scope: !1772)
!1818 = !DILocation(line: 71, column: 10, scope: !1772)
!1819 = !DILocation(line: 71, column: 22, scope: !1772)
!1820 = !DILocation(line: 71, column: 27, scope: !1772)
!1821 = !DILocation(line: 72, column: 7, scope: !1800)
!1822 = !DILocation(line: 72, column: 11, scope: !1800)
!1823 = !DILocation(line: 72, column: 7, scope: !1772)
!1824 = !DILocation(line: 73, column: 10, scope: !1798)
!1825 = !DILocation(line: 73, column: 17, scope: !1798)
!1826 = !DILocation(line: 73, column: 24, scope: !1803)
!1827 = !DILocation(line: 73, column: 28, scope: !1803)
!1828 = !DILocation(line: 73, column: 26, scope: !1803)
!1829 = !DILocation(line: 73, column: 5, scope: !1798)
!1830 = !DILocation(line: 73, column: 5, scope: !1803)
!1831 = !DILocation(line: 75, column: 7, scope: !1802)
!1832 = !DILocation(line: 75, column: 20, scope: !1802)
!1833 = !DILocation(line: 75, column: 25, scope: !1802)
!1834 = !DILocation(line: 75, column: 32, scope: !1802)
!1835 = !{i64 0, i64 4, !432, i64 4, i64 4, !359}
!1836 = !DILocation(line: 76, column: 7, scope: !1802)
!1837 = !DILocation(line: 77, column: 5, scope: !1803)
!1838 = !DILocation(line: 77, column: 5, scope: !1802)
!1839 = !DILocation(line: 73, column: 40, scope: !1803)
!1840 = distinct !{!1840, !1829, !1841}
!1841 = !DILocation(line: 77, column: 5, scope: !1798)
!1842 = !DILocation(line: 78, column: 3, scope: !1799)
!1843 = !DILocation(line: 79, column: 10, scope: !1772)
!1844 = !DILocation(line: 80, column: 1, scope: !1772)
!1845 = !DILocation(line: 79, column: 3, scope: !1772)
!1846 = distinct !DISubprogram(name: "send_msg", scope: !166, file: !166, line: 85, type: !1847, scopeLine: 85, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !1849)
!1847 = !DISubroutineType(types: !1848)
!1848 = !{!1775, !37, !1776}
!1849 = !{!1850, !1851, !1852, !1853, !1854, !1855, !1859}
!1850 = !DILocalVariable(name: "handle", arg: 1, scope: !1846, file: !166, line: 85, type: !37)
!1851 = !DILocalVariable(name: "msg", arg: 2, scope: !1846, file: !166, line: 85, type: !1776)
!1852 = !DILocalVariable(name: "ret", scope: !1846, file: !166, line: 88, type: !1775)
!1853 = !DILocalVariable(name: "iovecs", scope: !1846, file: !166, line: 89, type: !1782)
!1854 = !DILocalVariable(name: "iovec_cnt", scope: !1846, file: !166, line: 90, type: !33)
!1855 = !DILocalVariable(name: "i", scope: !1856, file: !166, line: 92, type: !33)
!1856 = distinct !DILexicalBlock(scope: !1857, file: !166, line: 92, column: 5)
!1857 = distinct !DILexicalBlock(scope: !1858, file: !166, line: 91, column: 17)
!1858 = distinct !DILexicalBlock(scope: !1846, file: !166, line: 91, column: 7)
!1859 = !DILocalVariable(name: "iv", scope: !1860, file: !166, line: 94, type: !1783)
!1860 = distinct !DILexicalBlock(scope: !1861, file: !166, line: 92, column: 44)
!1861 = distinct !DILexicalBlock(scope: !1856, file: !166, line: 92, column: 5)
!1862 = !DILocation(line: 85, column: 27, scope: !1846)
!1863 = !DILocation(line: 85, column: 46, scope: !1846)
!1864 = !DILocation(line: 87, column: 9, scope: !1846)
!1865 = !DILocation(line: 88, column: 3, scope: !1846)
!1866 = !DILocation(line: 88, column: 11, scope: !1846)
!1867 = !DILocation(line: 88, column: 17, scope: !1846)
!1868 = !DILocation(line: 89, column: 3, scope: !1846)
!1869 = !DILocation(line: 89, column: 17, scope: !1846)
!1870 = !DILocation(line: 89, column: 26, scope: !1846)
!1871 = !DILocation(line: 89, column: 31, scope: !1846)
!1872 = !DILocation(line: 90, column: 3, scope: !1846)
!1873 = !DILocation(line: 90, column: 10, scope: !1846)
!1874 = !DILocation(line: 90, column: 22, scope: !1846)
!1875 = !DILocation(line: 90, column: 27, scope: !1846)
!1876 = !DILocation(line: 91, column: 7, scope: !1858)
!1877 = !DILocation(line: 91, column: 11, scope: !1858)
!1878 = !DILocation(line: 91, column: 7, scope: !1846)
!1879 = !DILocation(line: 92, column: 10, scope: !1856)
!1880 = !DILocation(line: 92, column: 17, scope: !1856)
!1881 = !DILocation(line: 92, column: 24, scope: !1861)
!1882 = !DILocation(line: 92, column: 28, scope: !1861)
!1883 = !DILocation(line: 92, column: 26, scope: !1861)
!1884 = !DILocation(line: 92, column: 5, scope: !1856)
!1885 = !DILocation(line: 92, column: 5, scope: !1861)
!1886 = !DILocation(line: 94, column: 7, scope: !1860)
!1887 = !DILocation(line: 94, column: 20, scope: !1860)
!1888 = !DILocation(line: 94, column: 25, scope: !1860)
!1889 = !DILocation(line: 94, column: 32, scope: !1860)
!1890 = !DILocation(line: 95, column: 7, scope: !1860)
!1891 = !DILocation(line: 96, column: 5, scope: !1861)
!1892 = !DILocation(line: 96, column: 5, scope: !1860)
!1893 = !DILocation(line: 92, column: 40, scope: !1861)
!1894 = distinct !{!1894, !1884, !1895}
!1895 = !DILocation(line: 96, column: 5, scope: !1856)
!1896 = !DILocation(line: 97, column: 3, scope: !1857)
!1897 = !DILocation(line: 98, column: 10, scope: !1846)
!1898 = !DILocation(line: 99, column: 1, scope: !1846)
!1899 = !DILocation(line: 98, column: 3, scope: !1846)
!1900 = distinct !DISubprogram(name: "put_msg", scope: !166, file: !166, line: 104, type: !1901, scopeLine: 104, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !1903)
!1901 = !DISubroutineType(types: !1902)
!1902 = !{!19, !37, !24}
!1903 = !{!1904, !1905}
!1904 = !DILocalVariable(name: "handle", arg: 1, scope: !1900, file: !166, line: 104, type: !37)
!1905 = !DILocalVariable(name: "msg_id", arg: 2, scope: !1900, file: !166, line: 104, type: !24)
!1906 = !DILocation(line: 104, column: 22, scope: !1900)
!1907 = !DILocation(line: 104, column: 39, scope: !1900)
!1908 = !DILocation(line: 107, column: 9, scope: !1900)
!1909 = !DILocation(line: 108, column: 22, scope: !1900)
!1910 = !DILocation(line: 108, column: 36, scope: !1900)
!1911 = !DILocation(line: 108, column: 33, scope: !1900)
!1912 = !DILocation(line: 108, column: 19, scope: !1900)
!1913 = !DILocation(line: 109, column: 10, scope: !1900)
!1914 = !DILocation(line: 109, column: 3, scope: !1900)
!1915 = distinct !DISubprogram(name: "wait", scope: !166, file: !166, line: 116, type: !1916, scopeLine: 116, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !1925)
!1916 = !DISubroutineType(types: !1917)
!1917 = !{!19, !37, !1918, !24}
!1918 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !1919, size: 32)
!1919 = !DIDerivedType(tag: DW_TAG_typedef, name: "uevent_t", file: !6, line: 116, baseType: !1920)
!1920 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "uevent", file: !6, line: 112, size: 96, elements: !1921)
!1921 = !{!1922, !1923, !1924}
!1922 = !DIDerivedType(tag: DW_TAG_member, name: "handle", scope: !1920, file: !6, line: 113, baseType: !37, size: 32)
!1923 = !DIDerivedType(tag: DW_TAG_member, name: "event", scope: !1920, file: !6, line: 114, baseType: !24, size: 32, offset: 32)
!1924 = !DIDerivedType(tag: DW_TAG_member, name: "cookie", scope: !1920, file: !6, line: 115, baseType: !31, size: 32, offset: 64)
!1925 = !{!1926, !1927, !1928, !1929}
!1926 = !DILocalVariable(name: "handle", arg: 1, scope: !1915, file: !166, line: 116, type: !37)
!1927 = !DILocalVariable(name: "event", arg: 2, scope: !1915, file: !166, line: 116, type: !1918)
!1928 = !DILocalVariable(name: "timeout_msecs", arg: 3, scope: !1915, file: !166, line: 116, type: !24)
!1929 = !DILocalVariable(name: "ret", scope: !1915, file: !166, line: 118, type: !19)
!1930 = !DILocation(line: 116, column: 19, scope: !1915)
!1931 = !DILocation(line: 116, column: 37, scope: !1915)
!1932 = !DILocation(line: 116, column: 53, scope: !1915)
!1933 = !DILocation(line: 117, column: 9, scope: !1915)
!1934 = !DILocation(line: 118, column: 3, scope: !1915)
!1935 = !DILocation(line: 118, column: 7, scope: !1915)
!1936 = !DILocation(line: 118, column: 13, scope: !1915)
!1937 = !DILocation(line: 119, column: 7, scope: !1938)
!1938 = distinct !DILexicalBlock(scope: !1915, file: !166, line: 119, column: 7)
!1939 = !DILocation(line: 119, column: 11, scope: !1938)
!1940 = !DILocation(line: 119, column: 7, scope: !1915)
!1941 = !DILocation(line: 120, column: 21, scope: !1942)
!1942 = distinct !DILexicalBlock(scope: !1938, file: !166, line: 119, column: 24)
!1943 = !DILocation(line: 120, column: 5, scope: !1942)
!1944 = !DILocation(line: 120, column: 12, scope: !1942)
!1945 = !DILocation(line: 120, column: 19, scope: !1942)
!1946 = !DILocation(line: 121, column: 39, scope: !1942)
!1947 = !DILocation(line: 121, column: 46, scope: !1942)
!1948 = !DILocation(line: 121, column: 21, scope: !1942)
!1949 = !DILocation(line: 121, column: 5, scope: !1942)
!1950 = !DILocation(line: 121, column: 12, scope: !1942)
!1951 = !DILocation(line: 121, column: 19, scope: !1942)
!1952 = !DILocation(line: 122, column: 20, scope: !1942)
!1953 = !DILocation(line: 122, column: 5, scope: !1942)
!1954 = !DILocation(line: 122, column: 12, scope: !1942)
!1955 = !DILocation(line: 122, column: 18, scope: !1942)
!1956 = !DILocation(line: 123, column: 12, scope: !1942)
!1957 = !DILocation(line: 123, column: 19, scope: !1942)
!1958 = !DILocation(line: 123, column: 25, scope: !1942)
!1959 = !DILocation(line: 123, column: 5, scope: !1942)
!1960 = !DILocation(line: 124, column: 3, scope: !1942)
!1961 = !DILocation(line: 125, column: 10, scope: !1915)
!1962 = !DILocation(line: 126, column: 1, scope: !1915)
!1963 = !DILocation(line: 125, column: 3, scope: !1915)
!1964 = distinct !DISubprogram(name: "wait_any", scope: !166, file: !166, line: 138, type: !1965, scopeLine: 138, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !1967)
!1965 = !DISubroutineType(types: !1966)
!1966 = !{!19, !1918, !24}
!1967 = !{!1968, !1969, !1970, !1971, !1972}
!1968 = !DILocalVariable(name: "ev", arg: 1, scope: !1964, file: !166, line: 138, type: !1918)
!1969 = !DILocalVariable(name: "timeout_msecs", arg: 2, scope: !1964, file: !166, line: 138, type: !24)
!1970 = !DILocalVariable(name: "active_handle", scope: !1964, file: !166, line: 140, type: !37)
!1971 = !DILocalVariable(name: "event_flag", scope: !1964, file: !166, line: 141, type: !24)
!1972 = !DILocalVariable(name: "ret", scope: !1964, file: !166, line: 159, type: !19)
!1973 = !DILocation(line: 138, column: 24, scope: !1964)
!1974 = !DILocation(line: 138, column: 37, scope: !1964)
!1975 = !DILocation(line: 139, column: 9, scope: !1964)
!1976 = !DILocation(line: 140, column: 3, scope: !1964)
!1977 = !DILocation(line: 140, column: 12, scope: !1964)
!1978 = !DILocation(line: 141, column: 3, scope: !1964)
!1979 = !DILocation(line: 141, column: 12, scope: !1964)
!1980 = !DILocation(line: 143, column: 7, scope: !1981)
!1981 = distinct !DILexicalBlock(scope: !1964, file: !166, line: 143, column: 7)
!1982 = !DILocation(line: 143, column: 7, scope: !1964)
!1983 = !DILocation(line: 144, column: 21, scope: !1984)
!1984 = distinct !DILexicalBlock(scope: !1981, file: !166, line: 143, column: 33)
!1985 = !DILocation(line: 144, column: 19, scope: !1984)
!1986 = !DILocation(line: 145, column: 3, scope: !1984)
!1987 = !DILocation(line: 145, column: 14, scope: !1988)
!1988 = distinct !DILexicalBlock(scope: !1981, file: !166, line: 145, column: 14)
!1989 = !DILocation(line: 145, column: 14, scope: !1981)
!1990 = !DILocation(line: 146, column: 21, scope: !1991)
!1991 = distinct !DILexicalBlock(scope: !1988, file: !166, line: 145, column: 39)
!1992 = !DILocation(line: 146, column: 19, scope: !1991)
!1993 = !DILocation(line: 147, column: 3, scope: !1991)
!1994 = !DILocation(line: 147, column: 14, scope: !1995)
!1995 = distinct !DILexicalBlock(scope: !1988, file: !166, line: 147, column: 14)
!1996 = !DILocation(line: 147, column: 14, scope: !1988)
!1997 = !DILocation(line: 148, column: 21, scope: !1998)
!1998 = distinct !DILexicalBlock(scope: !1995, file: !166, line: 147, column: 43)
!1999 = !DILocation(line: 148, column: 19, scope: !1998)
!2000 = !DILocation(line: 149, column: 3, scope: !1998)
!2001 = !DILocation(line: 150, column: 21, scope: !2002)
!2002 = distinct !DILexicalBlock(scope: !1995, file: !166, line: 149, column: 10)
!2003 = !DILocation(line: 150, column: 19, scope: !2002)
!2004 = !DILocation(line: 152, column: 16, scope: !1964)
!2005 = !DILocation(line: 152, column: 3, scope: !1964)
!2006 = !DILocation(line: 152, column: 7, scope: !1964)
!2007 = !DILocation(line: 152, column: 14, scope: !1964)
!2008 = !DILocation(line: 153, column: 34, scope: !1964)
!2009 = !DILocation(line: 153, column: 38, scope: !1964)
!2010 = !DILocation(line: 153, column: 16, scope: !1964)
!2011 = !DILocation(line: 153, column: 3, scope: !1964)
!2012 = !DILocation(line: 153, column: 7, scope: !1964)
!2013 = !DILocation(line: 153, column: 14, scope: !1964)
!2014 = !DILocation(line: 155, column: 16, scope: !1964)
!2015 = !DILocation(line: 155, column: 14, scope: !1964)
!2016 = !DILocation(line: 156, column: 10, scope: !1964)
!2017 = !DILocation(line: 156, column: 21, scope: !1964)
!2018 = !DILocation(line: 156, column: 3, scope: !1964)
!2019 = !DILocation(line: 157, column: 15, scope: !1964)
!2020 = !DILocation(line: 157, column: 3, scope: !1964)
!2021 = !DILocation(line: 157, column: 7, scope: !1964)
!2022 = !DILocation(line: 157, column: 13, scope: !1964)
!2023 = !DILocation(line: 159, column: 3, scope: !1964)
!2024 = !DILocation(line: 159, column: 7, scope: !1964)
!2025 = !DILocation(line: 159, column: 13, scope: !1964)
!2026 = !DILocation(line: 160, column: 10, scope: !1964)
!2027 = !DILocation(line: 160, column: 14, scope: !1964)
!2028 = !DILocation(line: 160, column: 3, scope: !1964)
!2029 = !DILocation(line: 161, column: 10, scope: !1964)
!2030 = !DILocation(line: 162, column: 1, scope: !1964)
!2031 = !DILocation(line: 161, column: 3, scope: !1964)
!2032 = distinct !DISubprogram(name: "port_create", scope: !166, file: !166, line: 167, type: !2033, scopeLine: 168, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !2035)
!2033 = !DISubroutineType(types: !2034)
!2034 = !{!37, !46, !24, !24, !24}
!2035 = !{!2036, !2037, !2038, !2039, !2040}
!2036 = !DILocalVariable(name: "path", arg: 1, scope: !2032, file: !166, line: 167, type: !46)
!2037 = !DILocalVariable(name: "num_recv_bufs", arg: 2, scope: !2032, file: !166, line: 167, type: !24)
!2038 = !DILocalVariable(name: "recv_buf_size", arg: 3, scope: !2032, file: !166, line: 168, type: !24)
!2039 = !DILocalVariable(name: "flags", arg: 4, scope: !2032, file: !166, line: 168, type: !24)
!2040 = !DILocalVariable(name: "retval", scope: !2032, file: !166, line: 172, type: !37)
!2041 = !DILocation(line: 167, column: 34, scope: !2032)
!2042 = !DILocation(line: 167, column: 49, scope: !2032)
!2043 = !DILocation(line: 168, column: 31, scope: !2032)
!2044 = !DILocation(line: 168, column: 55, scope: !2032)
!2045 = !DILocation(line: 169, column: 9, scope: !2032)
!2046 = !DILocation(line: 170, column: 9, scope: !2032)
!2047 = !DILocation(line: 171, column: 9, scope: !2032)
!2048 = !DILocation(line: 172, column: 3, scope: !2032)
!2049 = !DILocation(line: 172, column: 12, scope: !2032)
!2050 = !DILocation(line: 172, column: 21, scope: !2032)
!2051 = !DILocation(line: 173, column: 7, scope: !2052)
!2052 = distinct !DILexicalBlock(scope: !2032, file: !166, line: 173, column: 7)
!2053 = !DILocation(line: 173, column: 14, scope: !2052)
!2054 = !DILocation(line: 173, column: 7, scope: !2032)
!2055 = !DILocation(line: 174, column: 12, scope: !2052)
!2056 = !DILocation(line: 174, column: 5, scope: !2052)
!2057 = !DILocation(line: 176, column: 10, scope: !2032)
!2058 = !DILocation(line: 178, column: 8, scope: !2059)
!2059 = distinct !DILexicalBlock(scope: !2032, file: !166, line: 178, column: 7)
!2060 = !DILocation(line: 178, column: 14, scope: !2059)
!2061 = !DILocation(line: 178, column: 43, scope: !2059)
!2062 = !DILocation(line: 179, column: 9, scope: !2059)
!2063 = !DILocation(line: 179, column: 15, scope: !2059)
!2064 = !DILocation(line: 178, column: 7, scope: !2032)
!2065 = !DILocation(line: 181, column: 12, scope: !2066)
!2066 = distinct !DILexicalBlock(scope: !2059, file: !166, line: 179, column: 45)
!2067 = !DILocation(line: 182, column: 3, scope: !2066)
!2068 = !DILocation(line: 182, column: 16, scope: !2069)
!2069 = distinct !DILexicalBlock(scope: !2059, file: !166, line: 182, column: 14)
!2070 = !DILocation(line: 182, column: 22, scope: !2069)
!2071 = !DILocation(line: 182, column: 51, scope: !2069)
!2072 = !DILocation(line: 183, column: 15, scope: !2069)
!2073 = !DILocation(line: 183, column: 21, scope: !2069)
!2074 = !DILocation(line: 182, column: 14, scope: !2059)
!2075 = !DILocation(line: 185, column: 12, scope: !2076)
!2076 = distinct !DILexicalBlock(scope: !2069, file: !166, line: 183, column: 51)
!2077 = !DILocation(line: 186, column: 3, scope: !2076)
!2078 = !DILocation(line: 187, column: 14, scope: !2032)
!2079 = !DILocation(line: 187, column: 3, scope: !2032)
!2080 = !DILocation(line: 188, column: 10, scope: !2032)
!2081 = !DILocation(line: 188, column: 3, scope: !2032)
!2082 = !DILocation(line: 189, column: 1, scope: !2032)
!2083 = distinct !DISubprogram(name: "set_cookie", scope: !166, file: !166, line: 194, type: !2084, scopeLine: 194, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !2086)
!2084 = !DISubroutineType(types: !2085)
!2085 = !{!19, !37, !31}
!2086 = !{!2087, !2088, !2089}
!2087 = !DILocalVariable(name: "handle", arg: 1, scope: !2083, file: !166, line: 194, type: !37)
!2088 = !DILocalVariable(name: "cookie", arg: 2, scope: !2083, file: !166, line: 194, type: !31)
!2089 = !DILocalVariable(name: "ret", scope: !2083, file: !166, line: 200, type: !19)
!2090 = !DILocation(line: 194, column: 25, scope: !2083)
!2091 = !DILocation(line: 194, column: 39, scope: !2083)
!2092 = !DILocation(line: 198, column: 24, scope: !2093)
!2093 = distinct !DILexicalBlock(scope: !2083, file: !166, line: 198, column: 7)
!2094 = !DILocation(line: 198, column: 8, scope: !2093)
!2095 = !DILocation(line: 198, column: 7, scope: !2083)
!2096 = !DILocation(line: 198, column: 34, scope: !2097)
!2097 = distinct !DILexicalBlock(scope: !2093, file: !166, line: 198, column: 33)
!2098 = !DILocation(line: 200, column: 3, scope: !2083)
!2099 = !DILocation(line: 200, column: 7, scope: !2083)
!2100 = !DILocation(line: 200, column: 13, scope: !2083)
!2101 = !DILocation(line: 201, column: 10, scope: !2083)
!2102 = !DILocation(line: 201, column: 14, scope: !2083)
!2103 = !DILocation(line: 201, column: 3, scope: !2083)
!2104 = !DILocation(line: 202, column: 7, scope: !2105)
!2105 = distinct !DILexicalBlock(scope: !2083, file: !166, line: 202, column: 7)
!2106 = !DILocation(line: 202, column: 11, scope: !2105)
!2107 = !DILocation(line: 202, column: 7, scope: !2083)
!2108 = !DILocation(line: 202, column: 36, scope: !2109)
!2109 = distinct !DILexicalBlock(scope: !2105, file: !166, line: 202, column: 17)
!2110 = !DILocation(line: 202, column: 44, scope: !2109)
!2111 = !DILocation(line: 202, column: 18, scope: !2109)
!2112 = !DILocation(line: 202, column: 52, scope: !2109)
!2113 = !DILocation(line: 203, column: 10, scope: !2083)
!2114 = !DILocation(line: 203, column: 3, scope: !2083)
!2115 = !DILocation(line: 204, column: 1, scope: !2083)
!2116 = distinct !DISubprogram(name: "accept", scope: !166, file: !166, line: 212, type: !2117, scopeLine: 212, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !2127)
!2117 = !DISubroutineType(types: !2118)
!2118 = !{!37, !37, !2119}
!2119 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !2120, size: 32)
!2120 = !DIDerivedType(tag: DW_TAG_typedef, name: "uuid_t", file: !132, line: 33, baseType: !2121)
!2121 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "uuid", file: !132, line: 28, size: 128, elements: !2122)
!2122 = !{!2123, !2124, !2125, !2126}
!2123 = !DIDerivedType(tag: DW_TAG_member, name: "time_low", scope: !2121, file: !132, line: 29, baseType: !24, size: 32)
!2124 = !DIDerivedType(tag: DW_TAG_member, name: "time_mid", scope: !2121, file: !132, line: 30, baseType: !137, size: 16, offset: 32)
!2125 = !DIDerivedType(tag: DW_TAG_member, name: "time_hi_and_version", scope: !2121, file: !132, line: 31, baseType: !137, size: 16, offset: 48)
!2126 = !DIDerivedType(tag: DW_TAG_member, name: "clock_seq_and_node", scope: !2121, file: !132, line: 32, baseType: !141, size: 64, offset: 64)
!2127 = !{!2128, !2129, !2130}
!2128 = !DILocalVariable(name: "port_handle", arg: 1, scope: !2116, file: !166, line: 212, type: !37)
!2129 = !DILocalVariable(name: "peer_uuid", arg: 2, scope: !2116, file: !166, line: 212, type: !2119)
!2130 = !DILocalVariable(name: "chan", scope: !2116, file: !166, line: 214, type: !37)
!2131 = !DILocation(line: 212, column: 26, scope: !2116)
!2132 = !DILocation(line: 212, column: 47, scope: !2116)
!2133 = !DILocation(line: 213, column: 9, scope: !2116)
!2134 = !DILocation(line: 214, column: 3, scope: !2116)
!2135 = !DILocation(line: 214, column: 12, scope: !2116)
!2136 = !DILocation(line: 214, column: 19, scope: !2116)
!2137 = !DILocation(line: 215, column: 7, scope: !2138)
!2138 = distinct !DILexicalBlock(scope: !2116, file: !166, line: 215, column: 7)
!2139 = !DILocation(line: 215, column: 12, scope: !2138)
!2140 = !DILocation(line: 215, column: 7, scope: !2116)
!2141 = !DILocation(line: 216, column: 14, scope: !2142)
!2142 = distinct !DILexicalBlock(scope: !2138, file: !166, line: 215, column: 18)
!2143 = !DILocation(line: 216, column: 19, scope: !2142)
!2144 = !DILocation(line: 216, column: 12, scope: !2142)
!2145 = !DILocation(line: 216, column: 5, scope: !2142)
!2146 = !DILocation(line: 218, column: 27, scope: !2142)
!2147 = !DILocation(line: 218, column: 5, scope: !2142)
!2148 = !DILocation(line: 218, column: 16, scope: !2142)
!2149 = !DILocation(line: 218, column: 25, scope: !2142)
!2150 = !{!2151, !360, i64 0}
!2151 = !{!"uuid", !360, i64 0, !2152, i64 4, !2152, i64 6, !361, i64 8}
!2152 = !{!"short", !361, i64 0}
!2153 = !DILocation(line: 219, column: 27, scope: !2142)
!2154 = !DILocation(line: 219, column: 5, scope: !2142)
!2155 = !DILocation(line: 219, column: 16, scope: !2142)
!2156 = !DILocation(line: 219, column: 25, scope: !2142)
!2157 = !{!2151, !2152, i64 4}
!2158 = !DILocation(line: 220, column: 38, scope: !2142)
!2159 = !DILocation(line: 220, column: 5, scope: !2142)
!2160 = !DILocation(line: 220, column: 16, scope: !2142)
!2161 = !DILocation(line: 220, column: 36, scope: !2142)
!2162 = !{!2151, !2152, i64 6}
!2163 = !DILocation(line: 221, column: 16, scope: !2142)
!2164 = !DILocation(line: 221, column: 5, scope: !2142)
!2165 = !DILocation(line: 222, column: 3, scope: !2142)
!2166 = !DILocation(line: 223, column: 10, scope: !2116)
!2167 = !DILocation(line: 224, column: 1, scope: !2116)
!2168 = !DILocation(line: 223, column: 3, scope: !2116)
!2169 = distinct !DISubprogram(name: "close", scope: !166, file: !166, line: 229, type: !2170, scopeLine: 229, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !157, retainedNodes: !2172)
!2170 = !DISubroutineType(types: !2171)
!2171 = !{!19, !37}
!2172 = !{!2173, !2174}
!2173 = !DILocalVariable(name: "handle", arg: 1, scope: !2169, file: !166, line: 229, type: !37)
!2174 = !DILocalVariable(name: "ret", scope: !2169, file: !166, line: 230, type: !19)
!2175 = !DILocation(line: 229, column: 20, scope: !2169)
!2176 = !DILocation(line: 230, column: 5, scope: !2169)
!2177 = !DILocation(line: 230, column: 9, scope: !2169)
!2178 = !DILocation(line: 230, column: 15, scope: !2169)
!2179 = !DILocation(line: 231, column: 12, scope: !2169)
!2180 = !DILocation(line: 231, column: 16, scope: !2169)
!2181 = !DILocation(line: 231, column: 5, scope: !2169)
!2182 = !DILocation(line: 232, column: 19, scope: !2169)
!2183 = !DILocation(line: 232, column: 5, scope: !2169)
!2184 = !DILocation(line: 233, column: 12, scope: !2169)
!2185 = !DILocation(line: 234, column: 1, scope: !2169)
!2186 = !DILocation(line: 233, column: 5, scope: !2169)
!2187 = distinct !DISubprogram(name: "realloc", scope: !2188, file: !2188, line: 9, type: !2189, scopeLine: 9, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !338, retainedNodes: !2191)
!2188 = !DIFile(filename: "seahorn/stubs/realloc.c", directory: "/home/s2priya/seahorn/verify-trusty/verifyTrusty")
!2189 = !DISubroutineType(types: !2190)
!2190 = !{!31, !31, !33}
!2191 = !{!2192, !2193}
!2192 = !DILocalVariable(name: "ptr", arg: 1, scope: !2187, file: !2188, line: 9, type: !31)
!2193 = !DILocalVariable(name: "new_size", arg: 2, scope: !2187, file: !2188, line: 9, type: !33)
!2194 = !DILocation(line: 9, column: 21, scope: !2187)
!2195 = !DILocation(line: 9, column: 33, scope: !2187)
!2196 = !DILocation(line: 10, column: 7, scope: !2197)
!2197 = distinct !DILexicalBlock(scope: !2187, file: !2188, line: 10, column: 7)
!2198 = !DILocation(line: 10, column: 7, scope: !2187)
!2199 = !DILocation(line: 10, column: 18, scope: !2200)
!2200 = distinct !DILexicalBlock(scope: !2197, file: !2188, line: 10, column: 12)
!2201 = !DILocation(line: 10, column: 13, scope: !2200)
!2202 = !DILocation(line: 10, column: 23, scope: !2200)
!2203 = !DILocation(line: 11, column: 16, scope: !2187)
!2204 = !DILocation(line: 11, column: 9, scope: !2187)
!2205 = !DILocation(line: 11, column: 7, scope: !2187)
!2206 = !DILocation(line: 12, column: 10, scope: !2187)
!2207 = !DILocation(line: 12, column: 3, scope: !2187)
!2208 = distinct !DISubprogram(name: "handle_table_init", scope: !225, file: !225, line: 15, type: !2209, scopeLine: 15, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !2211)
!2209 = !DISubroutineType(types: !2210)
!2210 = !{null, !37, !37, !37}
!2211 = !{!2212, !2213, !2214}
!2212 = !DILocalVariable(name: "secure_port", arg: 1, scope: !2208, file: !225, line: 15, type: !37)
!2213 = !DILocalVariable(name: "non_secure_port", arg: 2, scope: !2208, file: !225, line: 15, type: !37)
!2214 = !DILocalVariable(name: "channel", arg: 3, scope: !2208, file: !225, line: 15, type: !37)
!2215 = !DILocation(line: 15, column: 33, scope: !2208)
!2216 = !DILocation(line: 15, column: 55, scope: !2208)
!2217 = !DILocation(line: 15, column: 81, scope: !2208)
!2218 = !DILocation(line: 16, column: 29, scope: !2208)
!2219 = !DILocation(line: 16, column: 27, scope: !2208)
!2220 = !{!2221, !360, i64 0}
!2221 = !{!"handle_table", !360, i64 0, !1756, i64 4, !376, i64 8, !360, i64 12, !1756, i64 16, !376, i64 20, !360, i64 24, !1756, i64 28, !376, i64 32}
!2222 = !DILocation(line: 17, column: 36, scope: !2208)
!2223 = !DILocation(line: 17, column: 48, scope: !2208)
!2224 = !DILocation(line: 17, column: 34, scope: !2208)
!2225 = !{!2221, !1756, i64 4}
!2226 = !DILocation(line: 19, column: 33, scope: !2208)
!2227 = !DILocation(line: 19, column: 31, scope: !2208)
!2228 = !{!2221, !360, i64 12}
!2229 = !DILocation(line: 20, column: 40, scope: !2208)
!2230 = !DILocation(line: 20, column: 56, scope: !2208)
!2231 = !DILocation(line: 20, column: 38, scope: !2208)
!2232 = !{!2221, !1756, i64 16}
!2233 = !DILocation(line: 22, column: 22, scope: !2208)
!2234 = !DILocation(line: 22, column: 20, scope: !2208)
!2235 = !{!2221, !360, i64 24}
!2236 = !DILocation(line: 23, column: 29, scope: !2208)
!2237 = !DILocation(line: 23, column: 37, scope: !2208)
!2238 = !DILocation(line: 23, column: 27, scope: !2208)
!2239 = !{!2221, !1756, i64 28}
!2240 = !DILocation(line: 24, column: 5, scope: !2208)
!2241 = distinct !DISubprogram(name: "add_handle", scope: !225, file: !225, line: 29, type: !2242, scopeLine: 29, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !2244)
!2242 = !DISubroutineType(types: !2243)
!2243 = !{null, !37}
!2244 = !{!2245}
!2245 = !DILocalVariable(name: "handle", arg: 1, scope: !2241, file: !225, line: 29, type: !37)
!2246 = !DILocation(line: 29, column: 26, scope: !2241)
!2247 = !DILocation(line: 30, column: 7, scope: !2248)
!2248 = distinct !DILexicalBlock(scope: !2241, file: !225, line: 30, column: 7)
!2249 = !DILocation(line: 30, column: 7, scope: !2241)
!2250 = !DILocation(line: 31, column: 9, scope: !2251)
!2251 = distinct !DILexicalBlock(scope: !2252, file: !225, line: 31, column: 9)
!2252 = distinct !DILexicalBlock(scope: !2248, file: !225, line: 30, column: 31)
!2253 = !DILocation(line: 31, column: 9, scope: !2252)
!2254 = !DILocation(line: 32, column: 31, scope: !2255)
!2255 = distinct !DILexicalBlock(scope: !2251, file: !225, line: 31, column: 35)
!2256 = !DILocation(line: 32, column: 29, scope: !2255)
!2257 = !DILocation(line: 33, column: 36, scope: !2255)
!2258 = !DILocation(line: 34, column: 5, scope: !2255)
!2259 = !DILocation(line: 35, column: 35, scope: !2260)
!2260 = distinct !DILexicalBlock(scope: !2251, file: !225, line: 34, column: 12)
!2261 = !DILocation(line: 35, column: 33, scope: !2260)
!2262 = !DILocation(line: 36, column: 40, scope: !2260)
!2263 = !DILocation(line: 38, column: 3, scope: !2252)
!2264 = !DILocation(line: 39, column: 22, scope: !2265)
!2265 = distinct !DILexicalBlock(scope: !2248, file: !225, line: 38, column: 10)
!2266 = !DILocation(line: 39, column: 20, scope: !2265)
!2267 = !DILocation(line: 40, column: 27, scope: !2265)
!2268 = !DILocation(line: 42, column: 1, scope: !2241)
!2269 = distinct !DISubprogram(name: "remove_handle", scope: !225, file: !225, line: 44, type: !2242, scopeLine: 44, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !2270)
!2270 = !{!2271}
!2271 = !DILocalVariable(name: "handle", arg: 1, scope: !2269, file: !225, line: 44, type: !37)
!2272 = !DILocation(line: 44, column: 29, scope: !2269)
!2273 = !DILocation(line: 45, column: 7, scope: !2274)
!2274 = distinct !DILexicalBlock(scope: !2269, file: !225, line: 45, column: 7)
!2275 = !DILocation(line: 45, column: 20, scope: !2274)
!2276 = !DILocation(line: 45, column: 14, scope: !2274)
!2277 = !DILocation(line: 45, column: 7, scope: !2269)
!2278 = !DILocation(line: 46, column: 34, scope: !2279)
!2279 = distinct !DILexicalBlock(scope: !2274, file: !225, line: 45, column: 40)
!2280 = !DILocation(line: 47, column: 3, scope: !2279)
!2281 = !DILocation(line: 47, column: 14, scope: !2282)
!2282 = distinct !DILexicalBlock(scope: !2274, file: !225, line: 47, column: 14)
!2283 = !DILocation(line: 47, column: 27, scope: !2282)
!2284 = !DILocation(line: 47, column: 21, scope: !2282)
!2285 = !DILocation(line: 47, column: 14, scope: !2274)
!2286 = !DILocation(line: 48, column: 38, scope: !2287)
!2287 = distinct !DILexicalBlock(scope: !2282, file: !225, line: 47, column: 51)
!2288 = !DILocation(line: 49, column: 3, scope: !2287)
!2289 = !DILocation(line: 49, column: 14, scope: !2290)
!2290 = distinct !DILexicalBlock(scope: !2282, file: !225, line: 49, column: 14)
!2291 = !DILocation(line: 49, column: 27, scope: !2290)
!2292 = !DILocation(line: 49, column: 21, scope: !2290)
!2293 = !DILocation(line: 49, column: 14, scope: !2282)
!2294 = !DILocation(line: 50, column: 27, scope: !2295)
!2295 = distinct !DILexicalBlock(scope: !2290, file: !225, line: 49, column: 40)
!2296 = !DILocation(line: 51, column: 3, scope: !2295)
!2297 = !DILocation(line: 52, column: 1, scope: !2269)
!2298 = distinct !DISubprogram(name: "contains_handle", scope: !225, file: !225, line: 54, type: !2299, scopeLine: 54, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !2301)
!2299 = !DISubroutineType(types: !2300)
!2300 = !{!178, !37}
!2301 = !{!2302}
!2302 = !DILocalVariable(name: "handle", arg: 1, scope: !2298, file: !225, line: 54, type: !37)
!2303 = !DILocation(line: 54, column: 31, scope: !2298)
!2304 = !DILocation(line: 55, column: 7, scope: !2305)
!2305 = distinct !DILexicalBlock(scope: !2298, file: !225, line: 55, column: 7)
!2306 = !DILocation(line: 55, column: 20, scope: !2305)
!2307 = !DILocation(line: 55, column: 14, scope: !2305)
!2308 = !DILocation(line: 55, column: 7, scope: !2298)
!2309 = !DILocation(line: 56, column: 15, scope: !2310)
!2310 = distinct !DILexicalBlock(scope: !2305, file: !225, line: 55, column: 40)
!2311 = !{i8 0, i8 2}
!2312 = !DILocation(line: 56, column: 5, scope: !2310)
!2313 = !DILocation(line: 57, column: 14, scope: !2314)
!2314 = distinct !DILexicalBlock(scope: !2305, file: !225, line: 57, column: 14)
!2315 = !DILocation(line: 57, column: 27, scope: !2314)
!2316 = !DILocation(line: 57, column: 21, scope: !2314)
!2317 = !DILocation(line: 57, column: 14, scope: !2305)
!2318 = !DILocation(line: 58, column: 15, scope: !2319)
!2319 = distinct !DILexicalBlock(scope: !2314, file: !225, line: 57, column: 51)
!2320 = !DILocation(line: 58, column: 5, scope: !2319)
!2321 = !DILocation(line: 59, column: 14, scope: !2322)
!2322 = distinct !DILexicalBlock(scope: !2314, file: !225, line: 59, column: 14)
!2323 = !DILocation(line: 59, column: 27, scope: !2322)
!2324 = !DILocation(line: 59, column: 21, scope: !2322)
!2325 = !DILocation(line: 59, column: 14, scope: !2314)
!2326 = !DILocation(line: 60, column: 15, scope: !2327)
!2327 = distinct !DILexicalBlock(scope: !2322, file: !225, line: 59, column: 40)
!2328 = !DILocation(line: 60, column: 5, scope: !2327)
!2329 = !DILocation(line: 62, column: 3, scope: !2298)
!2330 = !DILocation(line: 63, column: 1, scope: !2298)
!2331 = distinct !DISubprogram(name: "get_handle_cookie", scope: !225, file: !225, line: 65, type: !2332, scopeLine: 65, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !2334)
!2332 = !DISubroutineType(types: !2333)
!2333 = !{!31, !37}
!2334 = !{!2335}
!2335 = !DILocalVariable(name: "handle", arg: 1, scope: !2331, file: !225, line: 65, type: !37)
!2336 = !DILocation(line: 65, column: 34, scope: !2331)
!2337 = !DILocation(line: 66, column: 7, scope: !2338)
!2338 = distinct !DILexicalBlock(scope: !2331, file: !225, line: 66, column: 7)
!2339 = !DILocation(line: 66, column: 20, scope: !2338)
!2340 = !DILocation(line: 66, column: 14, scope: !2338)
!2341 = !DILocation(line: 66, column: 7, scope: !2331)
!2342 = !DILocation(line: 67, column: 15, scope: !2343)
!2343 = distinct !DILexicalBlock(scope: !2338, file: !225, line: 66, column: 40)
!2344 = !{!2221, !376, i64 8}
!2345 = !DILocation(line: 67, column: 5, scope: !2343)
!2346 = !DILocation(line: 68, column: 14, scope: !2347)
!2347 = distinct !DILexicalBlock(scope: !2338, file: !225, line: 68, column: 14)
!2348 = !DILocation(line: 68, column: 27, scope: !2347)
!2349 = !DILocation(line: 68, column: 21, scope: !2347)
!2350 = !DILocation(line: 68, column: 14, scope: !2338)
!2351 = !DILocation(line: 69, column: 15, scope: !2352)
!2352 = distinct !DILexicalBlock(scope: !2347, file: !225, line: 68, column: 51)
!2353 = !{!2221, !376, i64 20}
!2354 = !DILocation(line: 69, column: 5, scope: !2352)
!2355 = !DILocation(line: 70, column: 14, scope: !2356)
!2356 = distinct !DILexicalBlock(scope: !2347, file: !225, line: 70, column: 14)
!2357 = !DILocation(line: 70, column: 27, scope: !2356)
!2358 = !DILocation(line: 70, column: 21, scope: !2356)
!2359 = !DILocation(line: 70, column: 14, scope: !2347)
!2360 = !DILocation(line: 71, column: 15, scope: !2361)
!2361 = distinct !DILexicalBlock(scope: !2356, file: !225, line: 70, column: 40)
!2362 = !{!2221, !376, i64 32}
!2363 = !DILocation(line: 71, column: 5, scope: !2361)
!2364 = !DILocation(line: 73, column: 3, scope: !2331)
!2365 = !DILocation(line: 74, column: 1, scope: !2331)
!2366 = distinct !DISubprogram(name: "set_handle_cookie", scope: !225, file: !225, line: 76, type: !2367, scopeLine: 76, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !2369)
!2367 = !DISubroutineType(types: !2368)
!2368 = !{null, !37, !31}
!2369 = !{!2370, !2371}
!2370 = !DILocalVariable(name: "handle", arg: 1, scope: !2366, file: !225, line: 76, type: !37)
!2371 = !DILocalVariable(name: "cookie", arg: 2, scope: !2366, file: !225, line: 76, type: !31)
!2372 = !DILocation(line: 76, column: 33, scope: !2366)
!2373 = !DILocation(line: 76, column: 47, scope: !2366)
!2374 = !DILocation(line: 77, column: 7, scope: !2375)
!2375 = distinct !DILexicalBlock(scope: !2366, file: !225, line: 77, column: 7)
!2376 = !DILocation(line: 77, column: 20, scope: !2375)
!2377 = !DILocation(line: 77, column: 14, scope: !2375)
!2378 = !DILocation(line: 77, column: 7, scope: !2366)
!2379 = !DILocation(line: 78, column: 29, scope: !2380)
!2380 = distinct !DILexicalBlock(scope: !2375, file: !225, line: 77, column: 40)
!2381 = !DILocation(line: 78, column: 27, scope: !2380)
!2382 = !DILocation(line: 79, column: 3, scope: !2380)
!2383 = !DILocation(line: 79, column: 14, scope: !2384)
!2384 = distinct !DILexicalBlock(scope: !2375, file: !225, line: 79, column: 14)
!2385 = !DILocation(line: 79, column: 27, scope: !2384)
!2386 = !DILocation(line: 79, column: 21, scope: !2384)
!2387 = !DILocation(line: 79, column: 14, scope: !2375)
!2388 = !DILocation(line: 80, column: 33, scope: !2389)
!2389 = distinct !DILexicalBlock(scope: !2384, file: !225, line: 79, column: 51)
!2390 = !DILocation(line: 80, column: 31, scope: !2389)
!2391 = !DILocation(line: 81, column: 3, scope: !2389)
!2392 = !DILocation(line: 81, column: 14, scope: !2393)
!2393 = distinct !DILexicalBlock(scope: !2384, file: !225, line: 81, column: 14)
!2394 = !DILocation(line: 81, column: 27, scope: !2393)
!2395 = !DILocation(line: 81, column: 21, scope: !2393)
!2396 = !DILocation(line: 81, column: 14, scope: !2384)
!2397 = !DILocation(line: 82, column: 22, scope: !2398)
!2398 = distinct !DILexicalBlock(scope: !2393, file: !225, line: 81, column: 40)
!2399 = !DILocation(line: 82, column: 20, scope: !2398)
!2400 = !DILocation(line: 83, column: 3, scope: !2398)
!2401 = !DILocation(line: 84, column: 1, scope: !2366)
!2402 = distinct !DISubprogram(name: "get_secure_port_handle", scope: !225, file: !225, line: 86, type: !2403, scopeLine: 86, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !39)
!2403 = !DISubroutineType(types: !2404)
!2404 = !{!37}
!2405 = !DILocation(line: 86, column: 50, scope: !2402)
!2406 = !DILocation(line: 86, column: 40, scope: !2402)
!2407 = distinct !DISubprogram(name: "get_non_secure_port_handle", scope: !225, file: !225, line: 87, type: !2403, scopeLine: 87, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !39)
!2408 = !DILocation(line: 87, column: 54, scope: !2407)
!2409 = !DILocation(line: 87, column: 44, scope: !2407)
!2410 = distinct !DISubprogram(name: "get_current_chan_handle", scope: !225, file: !225, line: 88, type: !2403, scopeLine: 88, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !39)
!2411 = !DILocation(line: 88, column: 51, scope: !2410)
!2412 = !DILocation(line: 88, column: 41, scope: !2410)
!2413 = distinct !DISubprogram(name: "is_secure_port_active", scope: !225, file: !225, line: 90, type: !188, scopeLine: 90, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !39)
!2414 = !DILocation(line: 90, column: 45, scope: !2413)
!2415 = !DILocation(line: 90, column: 35, scope: !2413)
!2416 = distinct !DISubprogram(name: "is_non_secure_port_active", scope: !225, file: !225, line: 91, type: !188, scopeLine: 91, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !39)
!2417 = !DILocation(line: 91, column: 49, scope: !2416)
!2418 = !DILocation(line: 91, column: 39, scope: !2416)
!2419 = distinct !DISubprogram(name: "is_current_chan_active", scope: !225, file: !225, line: 92, type: !188, scopeLine: 92, flags: DIFlagPrototyped | DIFlagAllCallsDescribed, spFlags: DISPFlagDefinition | DISPFlagOptimized, unit: !221, retainedNodes: !39)
!2420 = !DILocation(line: 92, column: 46, scope: !2419)
!2421 = !DILocation(line: 92, column: 36, scope: !2419)
