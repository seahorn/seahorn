// RUN: %sea bpf -O3 --bmc=mono --bound=5  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-bmc-crab=false --horn-bmc-muc=assume  --bmc=path --bound=5  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// -- Disabled because it takes too long
// %sea bpf -O3 --horn-bmc-crab=false --horn-bmc-muc=quickXplain  --bmc=path --bound=5  --horn-stats --inline --dsa=sea-ci "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-bmc-crab=true --horn-bmc-muc=assume  --bmc=path --bound=5  --horn-stats --inline --dsa=sea-ci "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-gsa --bmc=mono --bound=5  --horn-stats --inline --dsa=sea-ci "%s" 2>&1 | OutputCheck %s
// CHECK: ^unsat$

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);

int SendSrbSynchronous(int Extension , int Srb , int Buffer , int BufferLength );
int CdAudioSignalCompletion(int DeviceObject , int Irp , int Event );
int CdAudioStartDevice(int DeviceObject , int Irp );
int CdAudioPnp(int DeviceObject , int Irp );
int CdAudioDeviceControl(int DeviceObject , int Irp );
int CdAudioSendToNextDriver(int DeviceObject , int Irp );
int CdAudioIsPlayActive(int DeviceObject );
int CdAudio535DeviceControl(int DeviceObject , int Irp );
int AG_SetStatusAndReturn(int status , int Irp , int deviceExtension__TargetDeviceObject );
int CdAudio435DeviceControl(int DeviceObject , int Irp );
int CdAudioAtapiDeviceControl(int DeviceObject , int Irp );
int HPCdrCompletion(int DeviceObject , int Irp , int Context );
int CdAudioHPCdrDeviceControl(int DeviceObject , int Irp );
int CdAudioForwardIrpSynchronous(int DeviceObject , int Irp );
int CdAudioPower(int DeviceObject , int Irp );
int IofCallDriver(int DeviceObject , int Irp );
int KeSetEvent(int Event , int Increment , int Wait );
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable ,
                          int Timeout );
int PoCallDriver(int DeviceObject , int Irp );
int ZwClose(int Handle );
void IofCompleteRequest(int Irp , int PriorityBoost );
int __VERIFIER_nondet_int()  ;
int s  ;
int UNLOADED  ;
int NP  ;
int DC  ;
int SKIP1  ;
int SKIP2  ;
int MPR1  ;
int MPR3  ;
int IPC  ;
int pended  ;
int compFptr  ;
int compRegistered  ;
int lowerDriverReturn  ;
int setEventCalled  ;
int customIrp  ;
int routine  ;
int myStatus  ;
int pirp  ;
int Executive ;
int Suspended ;
int KernelMode ;
int DeviceUsageTypePaging ;

void errorFn(void) 
{ 

  {
  ERROR: __VERIFIER_error();
  return;
}
}
void _BLAST_init(void) 
{ 

  {
  UNLOADED = 0;
  NP = 1;
  DC = 2;
  SKIP1 = 3;
  SKIP2 = 4;
  MPR1 = 5;
  MPR3 = 6;
  IPC = 7;
  s = UNLOADED;
  pended = 0;
  compFptr = 0;
  compRegistered = 0;
  lowerDriverReturn = 0;
  setEventCalled = 0;
  customIrp = 0;
  return;
}
}
int SendSrbSynchronous(int Extension , int Srb , int Buffer , int BufferLength ) 
{ int ioStatus__Status = __VERIFIER_nondet_int() ;
  int ioctl ;
  int event = __VERIFIER_nondet_int() ;
  int irp ;
  int status = __VERIFIER_nondet_int() ;
  int __cil_tmp10 ;
  int __cil_tmp11 ;
  int __cil_tmp12 ;
  int __cil_tmp13 ;
  int __cil_tmp14 ;
  int __cil_tmp15 ;
  int __cil_tmp16 ;
  int __cil_tmp17 ;
  long __cil_tmp18 ;

  {
  irp = 0;
  if (Buffer) {
    __cil_tmp10 = 4116;
    __cil_tmp11 =  49152;
    __cil_tmp12 = 262144;
    __cil_tmp13 = 311296;
    ioctl = 315412;
  } else {
    __cil_tmp14 = 4100;
    __cil_tmp15 = 49152;
    __cil_tmp16 = 262144;
    __cil_tmp17 = 311296;
    ioctl = 315396;
  }
  if (! irp) {
    return (-1073741670);
  }
  {
  __cil_tmp18 = (long )status;
  if (__cil_tmp18 == 259L) {
    {
    KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
    status = ioStatus__Status;
    }
  }
  }
  return (status);
}
}
int CdAudioSignalCompletion(int DeviceObject , int Irp , int Event ) 
{ 

  {
  {
  KeSetEvent(Event, 0, 0);
  }
  return (-1073741802);
}
}
int CdAudioStartDevice(int DeviceObject , int Irp ) 
{ int deviceExtension__Active = __VERIFIER_nondet_int() ;
  int deviceExtension = __VERIFIER_nondet_int() ;
  int status ;
  int srb = __VERIFIER_nondet_int() ;
  int srb__Cdb = __VERIFIER_nondet_int() ;
  int cdb ;
  int inquiryDataPtr ;
  int attempt ;
  int tmp ;
  int deviceParameterHandle = __VERIFIER_nondet_int() ;
  int keyValue ;
  {
  {
  status = CdAudioForwardIrpSynchronous(DeviceObject, Irp);
  }
  {
  if (status < 0) {
    return (status);
  }
  }
  if (deviceExtension__Active == 255) {
    cdb = srb__Cdb;
    inquiryDataPtr = 0;
    attempt = 0;
    if (! inquiryDataPtr) {
      deviceExtension__Active = 0;
      return (0);
    }
    status = -1073741823;
    {
    while (1) {
      while_0_continue: /* CIL Label */ ;

      {
      if (status < 0) {
        tmp = attempt;
        attempt ++;
        if (tmp >= 4) {
          goto while_0_break_1;
        }
      } else {
        goto while_0_break_1;
      }
      }
      {
      status = SendSrbSynchronous(deviceExtension, srb, inquiryDataPtr, 36);
      }
    }
    while_0_break: /* CIL Label */ ;
    }
    while_0_break_1: ;
    {
    if (status < 0) {
      deviceExtension__Active = 0;
      return (0);
    }
    }
    deviceExtension__Active = 0;
  }
  keyValue = deviceExtension__Active;
  {
  if (status < 0) {
    return (0);
  }
  }
  {
  if (status < 0) {

  }
  }
  {
  ZwClose(deviceParameterHandle);
  }
  return (0);
}
}
int CdAudioPnp(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int irpSp__MinorFunction = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int irpSp__Parameters__UsageNotification__Type = __VERIFIER_nondet_int() ;
  int deviceExtension__PagingPathCountEvent = __VERIFIER_nondet_int() ;
  int irpSp__Parameters__UsageNotification__InPath = __VERIFIER_nondet_int() ;
  int deviceExtension__PagingPathCount = __VERIFIER_nondet_int() ;
  int DeviceObject__Flags ;
  int irpSp ;
  int status ;
  int setPagable ;
  int tmp ;
  int tmp___0 ;

  {
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
  status = -1073741637;
  if (irpSp__MinorFunction == 0) {
    goto switch_1_0;
  } else {
    if (irpSp__MinorFunction == 22) {
      goto switch_1_22;
    } else {
      goto switch_1_default;
      if (0) {
        switch_1_0: 
        {
        status = CdAudioStartDevice(DeviceObject, Irp);
        Irp__IoStatus__Status = status;
        myStatus = status;
        IofCompleteRequest(Irp, 0);
        }
        return (status);
        switch_1_22: ;
        if (irpSp__Parameters__UsageNotification__Type != DeviceUsageTypePaging) {
          {
          tmp = CdAudioSendToNextDriver(DeviceObject, Irp);
          }
          return (tmp);
        }
        {
        status = KeWaitForSingleObject(deviceExtension__PagingPathCountEvent, Executive,
                                       KernelMode, 0, 0);
        setPagable = 0;
        }
        if (irpSp__Parameters__UsageNotification__InPath) {
          if (deviceExtension__PagingPathCount != 1) {
            goto _L;
          }
        } else {
          _L: 
          if (status == status) {
            //DeviceObject__Flags |= 8192;
            setPagable = 1;
          }
        }
        {
        status = CdAudioForwardIrpSynchronous(DeviceObject, Irp);
        }
        if (status >= 0) {
          if (irpSp__Parameters__UsageNotification__InPath) {

          }
          if (irpSp__Parameters__UsageNotification__InPath) {
            if (deviceExtension__PagingPathCount == 1) {
              //DeviceObject__Flags &= -8193;
            }
          }
        } else {
          if (setPagable == 1) {
            //DeviceObject__Flags &= -8193;
            setPagable = 0;
          }
        }
        {
        KeSetEvent(deviceExtension__PagingPathCountEvent, 0, 0);
        IofCompleteRequest(Irp, 0);
        }
        return (status);
        goto switch_1_break;
        switch_1_default: 
        {
        tmp___0 = CdAudioSendToNextDriver(DeviceObject, Irp);
        }
        return (tmp___0);
      } else {
        switch_1_break: ;
      }
    }
  }
  return (0);
}
}
int CdAudioDeviceControl(int DeviceObject , int Irp ) 
{ int deviceExtension__Active = __VERIFIER_nondet_int() ;
  int status ;

  {
  if (deviceExtension__Active == 2) {
    goto switch_2_2;
  } else {
    if (deviceExtension__Active == 3) {
      goto switch_2_3;
    } else {
      if (deviceExtension__Active == 1) {
        goto switch_2_1;
      } else {
        if (deviceExtension__Active == 7) {
          goto switch_2_7;
        } else {
          goto switch_2_default;
          if (0) {
            switch_2_2: 
            {
            status = CdAudio535DeviceControl(DeviceObject, Irp);
            }
            goto switch_2_break;
            switch_2_3: 
            {
            status = CdAudio435DeviceControl(DeviceObject, Irp);
            }
            goto switch_2_break;
            switch_2_1: 
            {
            status = CdAudioAtapiDeviceControl(DeviceObject, Irp);
            }
            goto switch_2_break;
            switch_2_7: 
            {
            status = CdAudioHPCdrDeviceControl(DeviceObject, Irp);
            }
            goto switch_2_break;
            switch_2_default: 
            {
            deviceExtension__Active = 0;
            status = CdAudioSendToNextDriver(DeviceObject, Irp);
            }
          } else {
            switch_2_break: ;
          }
        }
      }
    }
  }
  return (status);
}
}
int CdAudioSendToNextDriver(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int tmp ;

  {
  if (s == NP) {
    s = SKIP1;
  } else {
    {
    errorFn();
    }
  }
  {
  Irp__CurrentLocation ++;
  Irp__Tail__Overlay__CurrentStackLocation ++;
  tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
  return (tmp);
}
}
int CdAudioIsPlayActive(int DeviceObject ) 
{ int deviceExtension__PlayActive = __VERIFIER_nondet_int() ;
  int ioStatus__Status = __VERIFIER_nondet_int() ;
  int currentBuffer__Header__AudioStatus = __VERIFIER_nondet_int() ;
  int irp_CdAudioIsPlayActive = __VERIFIER_nondet_int() ;
  int event = __VERIFIER_nondet_int() ;
  int status = __VERIFIER_nondet_int() ;
  int currentBuffer = __VERIFIER_nondet_int() ;
  int returnValue ;
  long __cil_tmp10 ;
  int __cil_tmp11 ;

  {
  if (! deviceExtension__PlayActive) {
    return (0);
  }
  if (currentBuffer == 0) {
    return (0);
  }
  if (irp_CdAudioIsPlayActive == 0) {
    return (0);
  }
  {
  __cil_tmp10 = (long )status;
  if (__cil_tmp10 == 259L) {
    {
    KeWaitForSingleObject(event, Suspended, KernelMode, 0, 0);
    status = ioStatus__Status;
    }
  }
  }
  {
  if (status < 0) {
    return (0);
  }
  }
  if (currentBuffer__Header__AudioStatus == 17) {
    returnValue = 1;
  } else {
    returnValue = 0;
    deviceExtension__PlayActive = 0;
  }
  return (returnValue);
}
}
int CdAudio535DeviceControl(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int Irp__AssociatedIrp__SystemBuffer = __VERIFIER_nondet_int() ;
  int srb__Cdb = __VERIFIER_nondet_int() ;
  int currentIrpStack__Parameters__DeviceIoControl__IoControlCode = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information ;
  int currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength = __VERIFIER_nondet_int() ;
  int currentIrpStack__Parameters__DeviceIoControl__InputBufferLength = __VERIFIER_nondet_int() ;
  int srb__CdbLength ;
  int cdb__CDB10__OperationCode ;
  int srb__TimeOutValue ;
  int sizeof__READ_CAPACITY_DATA = __VERIFIER_nondet_int() ;
  int lastSession__LogicalBlockAddress = __VERIFIER_nondet_int() ;
  int cdaudioDataOut__FirstTrack = __VERIFIER_nondet_int() ;
  int cdaudioDataOut__LastTrack = __VERIFIER_nondet_int() ;
  int sizeof__CDROM_TOC = __VERIFIER_nondet_int() ;
  int sizeof__SUB_Q_CURRENT_POSITION = __VERIFIER_nondet_int() ;
  int userPtr__Format = __VERIFIER_nondet_int() ;
  int sizeof__CDROM_PLAY_AUDIO_MSF = __VERIFIER_nondet_int() ;
  int inputBuffer__StartingM = __VERIFIER_nondet_int() ;
  int inputBuffer__EndingM = __VERIFIER_nondet_int() ;
  int inputBuffer__StartingS = __VERIFIER_nondet_int() ;
  int inputBuffer__EndingS = __VERIFIER_nondet_int() ;
  int inputBuffer__StartingF = __VERIFIER_nondet_int() ;
  int inputBuffer__EndingF = __VERIFIER_nondet_int() ;
  int cdb__PLAY_AUDIO_MSF__OperationCode = __VERIFIER_nondet_int() ;
  int sizeof__CDROM_SEEK_AUDIO_MSF = __VERIFIER_nondet_int() ;
  int currentIrpStack ;
  int deviceExtension ;
  int cdaudioDataOut ;
  int srb = __VERIFIER_nondet_int() ;
  int lastSession = __VERIFIER_nondet_int() ;
  int cdb ;
  int status ;
  int i = __VERIFIER_nondet_int() ;
  int bytesTransfered = __VERIFIER_nondet_int() ;
  int Toc = __VERIFIER_nondet_int() ;
  int tmp ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  int tmp___3 ;
  int tmp___4 ;
  int tracksToReturn ;
  int tracksOnCd ;
  int tracksInBuffer ;
  int userPtr ;
  int SubQPtr = __VERIFIER_nondet_int() ;
  int tmp___5 ;
  int tmp___6 ;
  int inputBuffer ;
  int inputBuffer___0 ;
  int tmp___7 ;
  int tmp___8 ;
  int __cil_tmp58 ;
  int __cil_tmp59 ;
  int __cil_tmp60 ;
  int __cil_tmp61 ;
  int __cil_tmp62 ;
  int __cil_tmp63 ;
  int __cil_tmp64 ;
  int __cil_tmp65 ;
  int __cil_tmp66 ;
  int __cil_tmp67 ;
  int __cil_tmp68 ;
  int __cil_tmp69 ;
  int __cil_tmp70 ;
  int __cil_tmp71 ;
  int __cil_tmp72 ;
  int __cil_tmp73 ;
  int __cil_tmp74 ;
  int __cil_tmp75 ;
  int __cil_tmp76 ;
  int __cil_tmp77 ;
  int __cil_tmp78 ;
  int __cil_tmp79 ;
  int __cil_tmp80 ;
  int __cil_tmp81 ;
  int __cil_tmp82 ;
  int __cil_tmp83 ;
  int __cil_tmp84 ;
  int __cil_tmp85 ;
  int __cil_tmp86 ;
  int __cil_tmp87 ;
  int __cil_tmp88 ;
  int __cil_tmp89 ;
  int __cil_tmp90 ;
  int __cil_tmp91 ;
  int __cil_tmp92 ;
  int __cil_tmp93 ;
  int __cil_tmp94 ;
  int __cil_tmp95 ;
  int __cil_tmp96 ;
  int __cil_tmp97 ;
  int __cil_tmp98 ;
  int __cil_tmp99 ;
  int __cil_tmp100 ;
  int __cil_tmp101 ;
  int __cil_tmp102 ;
  int __cil_tmp103 ;
  int __cil_tmp104 ;
  int __cil_tmp105 ;
  int __cil_tmp106 ;
  unsigned long __cil_tmp107 ;
  unsigned long __cil_tmp108 ;
  int __cil_tmp109 ;
  int __cil_tmp110 ;

  {
  currentIrpStack = Irp__Tail__Overlay__CurrentStackLocation;
  deviceExtension = DeviceObject__DeviceExtension;
  cdaudioDataOut = Irp__AssociatedIrp__SystemBuffer;
  cdb = srb__Cdb;
  {
  __cil_tmp58 = 56;
  __cil_tmp59 = 16384;
  __cil_tmp60 = 131072;
  __cil_tmp61 = 147456;
  __cil_tmp62 = 147512;
  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp62) {
    goto switch_3_exp_0;
  } else {
    {
    __cil_tmp63 = 16384;
    __cil_tmp64 = 131072;
    __cil_tmp65 = 147456;
    if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp65) {
      goto switch_3_exp_1;
    } else {
      {
      __cil_tmp66 = 44;
      __cil_tmp67 = 16384;
      __cil_tmp68 = 131072;
      __cil_tmp69 = 147456;
      __cil_tmp70 = 147500;
      if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp70) {
        goto switch_3_exp_2;
      } else {
        {
        __cil_tmp71 = 24;
        __cil_tmp72 = 16384;
        __cil_tmp73 = 131072;
        __cil_tmp74 = 147456;
        __cil_tmp75 = 147480;
        if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp75) {
          goto switch_3_exp_3;
        } else {
          {
          __cil_tmp76 = 4;
          __cil_tmp77 = 16384;
          __cil_tmp78 = 131072;
          __cil_tmp79 = 147456;
          __cil_tmp80 = 147460;
          if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp80) {
            goto switch_3_exp_4;
          } else {
            {
            __cil_tmp81 = 2056;
            __cil_tmp82 = 16384;
            __cil_tmp83 = 131072;
            __cil_tmp84 = 147456;
            __cil_tmp85 = 149512;
            if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp85) {
              goto switch_3_exp_5;
            } else {
              {
              __cil_tmp86 = 52;
              __cil_tmp87 = 16384;
              __cil_tmp88 = 131072;
              __cil_tmp89 = 147456;
              __cil_tmp90 = 147508;
              if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp90) {
                goto switch_3_exp_6;
              } else {
                {
                __cil_tmp91 = 20;
                __cil_tmp92 = 16384;
                __cil_tmp93 = 131072;
                __cil_tmp94 = 147456;
                __cil_tmp95 = 147476;
                if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp95) {
                  goto switch_3_exp_7;
                } else {
                  {
                  __cil_tmp96 = 40;
                  __cil_tmp97 = 16384;
                  __cil_tmp98 = 131072;
                  __cil_tmp99 = 147456;
                  __cil_tmp100 = 147496;
                  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp100) {
                    goto switch_3_exp_8;
                  } else {
                    {
                    __cil_tmp101 = 2048;
                    __cil_tmp102 = 16384;
                    __cil_tmp103 = 131072;
                    __cil_tmp104 = 147456;
                    __cil_tmp105 = 149504;
                    if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp105) {
                      goto switch_3_exp_9;
                    } else {
                      goto switch_3_default;
                      if (0) {
                        switch_3_exp_0: 
                        {
                        tmp = CdAudioIsPlayActive(DeviceObject);
                        }
                        if (tmp) {
                          status = -2147483631;
                          Irp__IoStatus__Information = 0;
                          goto switch_3_break;
                        }
                        if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength) {
                          status = -1073741789;
                          Irp__IoStatus__Information = 0;
                          goto switch_3_break;
                        }
                        if (lastSession == 0) {
                          {
                          status = -1073741670;
                          Irp__IoStatus__Information = 0;
                          tmp___0 = AG_SetStatusAndReturn(status, Irp, deviceExtension__TargetDeviceObject);
                          }
                          return (tmp___0);
                        }
                        {
                        srb__CdbLength = 10;
                        cdb__CDB10__OperationCode = 38;
                        srb__TimeOutValue = 10;
                        status = SendSrbSynchronous(deviceExtension, srb, lastSession,
                                                    sizeof__READ_CAPACITY_DATA);
                        }
                        {
                        if (status < 0) {
                          {
                          Irp__IoStatus__Information = 0;
                          tmp___1 = AG_SetStatusAndReturn(status, Irp, deviceExtension__TargetDeviceObject);
                          }
                          return (tmp___1);
                        } else {
                          status = 0;
                        }
                        }
                        Irp__IoStatus__Information = bytesTransfered;
                        if (lastSession__LogicalBlockAddress == 0) {
                          goto switch_3_break;
                        }
                        cdaudioDataOut__FirstTrack = 1;
                        cdaudioDataOut__LastTrack = 2;
                        goto switch_3_break;
                        switch_3_exp_1: ;
                        if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength) {
                          status = -1073741789;
                          Irp__IoStatus__Information = 0;
                          goto switch_3_break;
                        }
                        {
                        tmp___2 = CdAudioIsPlayActive(DeviceObject);
                        }
                        if (tmp___2) {
                          status = -2147483631;
                          Irp__IoStatus__Information = 0;
                          goto switch_3_break;
                        }
                        if (Toc == 0) {
                          {
                          status = -1073741670;
                          Irp__IoStatus__Information = 0;
                          tmp___3 = AG_SetStatusAndReturn(status, Irp, deviceExtension__TargetDeviceObject);
                          }
                          return (tmp___3);
                        }
                        {
                        srb__TimeOutValue = 10;
                        srb__CdbLength = 10;
                        status = SendSrbSynchronous(deviceExtension, srb, Toc, sizeof__CDROM_TOC);
                        }
                        if (status >= 0) {
                          {
                          __cil_tmp107 = (unsigned long )status;
                          if (__cil_tmp107 != -1073741764) {
                            status = 0;
                          } else {
                            goto _L;
                          }
                          }
                        } else {
                          _L: 
                          {
                          __cil_tmp108 = (unsigned long )status;
                          if (__cil_tmp108 != -1073741764) {
                            {
                            Irp__IoStatus__Information = 0;
                            tmp___4 = AG_SetStatusAndReturn(status, Irp, deviceExtension__TargetDeviceObject);
                            }
                            return (tmp___4);
                          }
                          }
                        }
                        __cil_tmp109 = cdaudioDataOut__LastTrack - cdaudioDataOut__FirstTrack;
                        tracksOnCd = __cil_tmp109 + 1;
                        tracksInBuffer = currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength;
                        if (tracksInBuffer < tracksOnCd) {
                          tracksToReturn = tracksInBuffer;
                        } else {
                          tracksToReturn = tracksOnCd;
                        }
                        if (tracksInBuffer > tracksOnCd) {
                          i ++;
                        }
                        goto switch_3_break;
                        switch_3_exp_2: 
                        userPtr = Irp__AssociatedIrp__SystemBuffer;
                        if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength < sizeof__SUB_Q_CURRENT_POSITION) {
                          status = -1073741789;
                          Irp__IoStatus__Information = 0;
                          goto switch_3_break;
                        }
                        if (SubQPtr == 0) {
                          {
                          status = -1073741670;
                          Irp__IoStatus__Information = 0;
                          tmp___5 = AG_SetStatusAndReturn(status, Irp, deviceExtension__TargetDeviceObject);
                          }
                          return (tmp___5);
                        }
                        if (userPtr__Format != 1) {
                          {
                          status = -1073741823;
                          Irp__IoStatus__Information = 0;
                          tmp___6 = AG_SetStatusAndReturn(status, Irp, deviceExtension__TargetDeviceObject);
                          }
                          return (tmp___6);
                        }
                        {
                        srb__CdbLength = 10;
                        srb__TimeOutValue = 10;
                        status = SendSrbSynchronous(deviceExtension, srb, SubQPtr,
                                                    sizeof__SUB_Q_CURRENT_POSITION);
                        }
                        if (status >= 0) {
                          Irp__IoStatus__Information = sizeof__SUB_Q_CURRENT_POSITION;
                        } else {
                          Irp__IoStatus__Information = 0;
                        }
                        goto switch_3_break;
                        switch_3_exp_3: 
                        inputBuffer = Irp__AssociatedIrp__SystemBuffer;
                        Irp__IoStatus__Information = 0;
                        if (currentIrpStack__Parameters__DeviceIoControl__InputBufferLength < sizeof__CDROM_PLAY_AUDIO_MSF) {
                          status = -1073741820;
                          goto switch_3_break;
                        }
                        if (inputBuffer__StartingM == inputBuffer__EndingM) {
                          if (inputBuffer__StartingS == inputBuffer__EndingS) {
                            if (inputBuffer__StartingF == inputBuffer__EndingF) {

                            }
                          }
                        }
                        {
                        srb__CdbLength = 10;
                        srb__TimeOutValue = 10;
                        status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                        }
                        if (status >= 0) {
                          if (cdb__PLAY_AUDIO_MSF__OperationCode == 71) {

                          }
                        }
                        goto switch_3_break;
                        switch_3_exp_4: 
                        inputBuffer___0 = Irp__AssociatedIrp__SystemBuffer;
                        Irp__IoStatus__Information = 0;
                        if (currentIrpStack__Parameters__DeviceIoControl__InputBufferLength < sizeof__CDROM_SEEK_AUDIO_MSF) {
                          status = -1073741820;
                          goto switch_3_break;
                        }
                        {
                        srb__CdbLength = 10;
                        srb__TimeOutValue = 10;
                        status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                        }
                        {
                        if (status < 0) {

                        }
                        }
                        goto switch_3_break;
                        switch_3_exp_5: 
                        {
                        Irp__IoStatus__Information = 0;
                        srb__CdbLength = 10;
                        srb__TimeOutValue = 10;
                        status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                        }
                        goto switch_3_break;
                        switch_3_exp_6: ;
                        switch_3_exp_7: ;
                        switch_3_exp_8: 
                        Irp__IoStatus__Information = 0;
                        status = -1073741808;
                        goto switch_3_break;
                        switch_3_exp_9: 
                        {
                        CdAudioIsPlayActive(DeviceObject);
                        }
                        switch_3_default: 
                        {
                        tmp___7 = CdAudioSendToNextDriver(DeviceObject, Irp);
                        }
                        return (tmp___7);
                        goto switch_3_break;
                      } else {
                        switch_3_break: ;
                      }
                    }
                    }
                  }
                  }
                }
                }
              }
              }
            }
            }
          }
          }
        }
        }
      }
      }
    }
    }
  }
  }
  {
  tmp___8 = AG_SetStatusAndReturn(status, Irp, deviceExtension__TargetDeviceObject);
  }
  return (tmp___8);
}
}
int AG_SetStatusAndReturn(int status , int Irp , int deviceExtension__TargetDeviceObject ) 
{ unsigned long __cil_tmp4 ;

  {
  {
  __cil_tmp4 = (unsigned long )status;
  if (__cil_tmp4 == -2147483626) {

  }
  }
  {
  myStatus = status;
  IofCompleteRequest(Irp, 0);
  }
  return (status);
}
}
int CdAudio435DeviceControl(int DeviceObject , int Irp ) 
{ int currentIrpStack__Parameters__DeviceIoControl__IoControlCode = __VERIFIER_nondet_int() ;
  int currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength = __VERIFIER_nondet_int() ;
  int currentIrpStack__Parameters__DeviceIoControl__InputBufferLength = __VERIFIER_nondet_int() ;
  int TrackData__0 = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information ;
  int srb__TimeOutValue ;
  int srb__CdbLength ;
  int sizeof__CDROM_TOC = __VERIFIER_nondet_int() ;
  int cdaudioDataOut__LastTrack = __VERIFIER_nondet_int() ;
  int cdaudioDataOut__FirstTrack = __VERIFIER_nondet_int() ;
  int sizeof__CDROM_PLAY_AUDIO_MSF = __VERIFIER_nondet_int() ;
  int sizeof__CDROM_SEEK_AUDIO_MSF = __VERIFIER_nondet_int() ;
  int deviceExtension__Paused = __VERIFIER_nondet_int() ;
  int deviceExtension__PlayActive ;
  int sizeof__SUB_Q_CHANNEL_DATA = __VERIFIER_nondet_int() ;
  int sizeof__SUB_Q_CURRENT_POSITION = __VERIFIER_nondet_int() ;
  int deviceExtension = __VERIFIER_nondet_int() ;
  int srb = __VERIFIER_nondet_int() ;
  int status ;
  int i = __VERIFIER_nondet_int() ;
  int bytesTransfered ;
  int Toc = __VERIFIER_nondet_int() ;
  int tmp ;
  int tracksToReturn ;
  int tracksOnCd ;
  int tracksInBuffer ;
  int SubQPtr = __VERIFIER_nondet_int() ;
  int userPtr__Format = __VERIFIER_nondet_int() ;
  int SubQPtr___0 = __VERIFIER_nondet_int() ;
  int tmp___0 ;
  int tmp___1 ;
  int tmp___2 ;
  int __cil_tmp35 ;
  int __cil_tmp36 ;
  int __cil_tmp37 ;
  int __cil_tmp38 ;
  int __cil_tmp39 ;
  int __cil_tmp40 ;
  int __cil_tmp41 ;
  int __cil_tmp42 ;
  int __cil_tmp43 ;
  int __cil_tmp44 ;
  int __cil_tmp45 ;
  int __cil_tmp46 ;
  int __cil_tmp47 ;
  int __cil_tmp48 ;
  int __cil_tmp49 ;
  int __cil_tmp50 ;
  int __cil_tmp51 ;
  int __cil_tmp52 ;
  int __cil_tmp53 ;
  int __cil_tmp54 ;
  int __cil_tmp55 ;
  int __cil_tmp56 ;
  int __cil_tmp57 ;
  int __cil_tmp58 ;
  int __cil_tmp59 ;
  int __cil_tmp60 ;
  int __cil_tmp61 ;
  int __cil_tmp62 ;
  int __cil_tmp63 ;
  int __cil_tmp64 ;
  int __cil_tmp65 ;
  int __cil_tmp66 ;
  int __cil_tmp67 ;
  int __cil_tmp68 ;
  int __cil_tmp69 ;
  int __cil_tmp70 ;
  int __cil_tmp71 ;
  int __cil_tmp72 ;
  int __cil_tmp73 ;
  int __cil_tmp74 ;
  int __cil_tmp75 ;
  int __cil_tmp76 ;
  int __cil_tmp77 ;
  int __cil_tmp78 ;
  int __cil_tmp79 ;
  int __cil_tmp80 ;
  int __cil_tmp81 ;
  int __cil_tmp82 ;
  int __cil_tmp83 ;
  int __cil_tmp84 ;
  int __cil_tmp85 ;
  int __cil_tmp86 ;
  int __cil_tmp87 ;
  int __cil_tmp88 ;
  int __cil_tmp89 ;
  int __cil_tmp90 ;
  int __cil_tmp91 ;
  int __cil_tmp92 ;
  unsigned long __cil_tmp93 ;
  int __cil_tmp94 ;
  unsigned long __cil_tmp95 ;
  unsigned long __cil_tmp96 ;
  unsigned long __cil_tmp97 ;
  int __cil_tmp98 ;
  int __cil_tmp99 ;
  int __cil_tmp100 ;
  int __cil_tmp101 ;
  int __cil_tmp102 ;
  int __cil_tmp103 ;
  unsigned long __cil_tmp104 ;
  unsigned long __cil_tmp105 ;
  unsigned long __cil_tmp106 ;
  unsigned long __cil_tmp107 ;
  int __cil_tmp108 ;
  unsigned long __cil_tmp109 ;
  int __cil_tmp110 ;
  unsigned long __cil_tmp111 ;
  unsigned long __cil_tmp112 ;
  unsigned long __cil_tmp113 ;
  unsigned long __cil_tmp114 ;
  unsigned long __cil_tmp115 ;
  unsigned long __cil_tmp116 ;

  {
  {
  __cil_tmp35 = 16384;
  __cil_tmp36 = 131072;
  __cil_tmp37 = 147456;
  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp37) {
    goto switch_4_exp_10;
  } else {
    {
    __cil_tmp38 = 24;
    __cil_tmp39 = 16384;
    __cil_tmp40 = 131072;
    __cil_tmp41 = 147456;
    __cil_tmp42 = 147480;
    if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp42) {
      goto switch_4_exp_11;
    } else {
      {
      __cil_tmp43 = 8;
      __cil_tmp44 = 16384;
      __cil_tmp45 = 131072;
      __cil_tmp46 = 147456;
      __cil_tmp47 = 147464;
      if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp47) {
        goto switch_4_exp_12;
      } else {
        {
        __cil_tmp48 = 4;
        __cil_tmp49 = 16384;
        __cil_tmp50 = 131072;
        __cil_tmp51 = 147456;
        __cil_tmp52 = 147460;
        if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp52) {
          goto switch_4_exp_13;
        } else {
          {
          __cil_tmp53 = 12;
          __cil_tmp54 = 16384;
          __cil_tmp55 = 131072;
          __cil_tmp56 = 147456;
          __cil_tmp57 = 147468;
          if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp57) {
            goto switch_4_exp_14;
          } else {
            {
            __cil_tmp58 = 16;
            __cil_tmp59 = 16384;
            __cil_tmp60 = 131072;
            __cil_tmp61 = 147456;
            __cil_tmp62 = 147472;
            if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp62) {
              goto switch_4_exp_15;
            } else {
              {
              __cil_tmp63 =  44;
              __cil_tmp64 = 16384;
              __cil_tmp65 = 131072;
              __cil_tmp66 = 147456;
              __cil_tmp67 = 147500;
              if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp67) {
                goto switch_4_exp_16;
              } else {
                {
                __cil_tmp68 = 2056;
                __cil_tmp69 = 16384;
                __cil_tmp70 = 131072;
                __cil_tmp71 = 147456;
                __cil_tmp72 = 149512;
                if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp72) {
                  goto switch_4_exp_17;
                } else {
                  {
                  __cil_tmp73 = 52;
                  __cil_tmp74 = 16384;
                  __cil_tmp75 = 131072;
                  __cil_tmp76 = 147456;
                  __cil_tmp77 = 147508;
                  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp77) {
                    goto switch_4_exp_18;
                  } else {
                    {
                    __cil_tmp78 = 20;
                    __cil_tmp79 = 16384;
                    __cil_tmp80 = 131072;
                    __cil_tmp81 = 147456;
                    __cil_tmp82 = 147476;
                    if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp82) {
                      goto switch_4_exp_19;
                    } else {
                      {
                      __cil_tmp83 = 40;
                      __cil_tmp84 = 16384;
                      __cil_tmp85 = 131072;
                      __cil_tmp86 = 147456;
                      __cil_tmp87 = 147496;
                      if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp87) {
                        goto switch_4_exp_20;
                      } else {
                        {
                        __cil_tmp88 = 2048;
                        __cil_tmp89 = 16384;
                        __cil_tmp90 = 131072;
                        __cil_tmp91 = 147456;
                        __cil_tmp92 = 149504;
                        if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp92) {
                          goto switch_4_exp_21;
                        } else {
                          goto switch_4_default;
                          if (0) {
                            switch_4_exp_10: ;
                            if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength < TrackData__0) {
                              status = -1073741789;
                              Irp__IoStatus__Information = 0;
                              goto switch_4_break;
                            }
                            {
                            tmp = CdAudioIsPlayActive(DeviceObject);
                            }
                            if (tmp) {
                              status = -2147483631;
                              Irp__IoStatus__Information = 0;
                              goto switch_4_break;
                            }
                            if (Toc == 0) {
                              status = -1073741670;
                              Irp__IoStatus__Information = 0;
                              {
                              __cil_tmp93 = (unsigned long )status;
                              if (__cil_tmp93 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            {
                            srb__TimeOutValue = 10;
                            srb__CdbLength = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, Toc,
                                                        sizeof__CDROM_TOC);
                            }
                            {
                            if (status < 0) {
                              {
                              __cil_tmp95 = (unsigned long )status;
                              if (__cil_tmp95 != -1073741764) {
                                {
                                __cil_tmp96 = (unsigned long )status;
                                if (__cil_tmp96 != -1073741764) {
                                  {
                                  __cil_tmp97 = (unsigned long )status;
                                  if (__cil_tmp97 == -2147483626) {
                                    Irp__IoStatus__Information = 0;
                                  }
                                  }
                                  {
                                  myStatus = status;
                                  IofCompleteRequest(Irp, 0);
                                  }
                                  return (status);
                                }
                                }
                              } else {
                                status = 0;
                              }
                              }
                            } else {
                              status = 0;
                            }
                            }
                            if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength > sizeof__CDROM_TOC) {
                              bytesTransfered = sizeof__CDROM_TOC;
                            } else {
                              bytesTransfered = currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength;
                            }
                            __cil_tmp98 = cdaudioDataOut__LastTrack - cdaudioDataOut__FirstTrack;
                            tracksOnCd = __cil_tmp98 + 1;
                            tracksInBuffer = currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength - TrackData__0;
                            if (tracksInBuffer < tracksOnCd) {
                              tracksToReturn = tracksInBuffer;
                            } else {
                              tracksToReturn = tracksOnCd;
                            }
                            if (tracksInBuffer > tracksOnCd) {
                              i ++;
                            }
                            goto switch_4_break;
                            switch_4_exp_11: ;
                            switch_4_exp_12: 
                            {
                            Irp__IoStatus__Information = 0;
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                            }
                            if (status >= 0) {

                            }
                            {
                            __cil_tmp99 = 8;
                            __cil_tmp100 = 16384;
                            __cil_tmp101 = 131072;
                            __cil_tmp102 = 147456;
                            __cil_tmp103 = 147464;
                            if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp103) {
                              {
                              __cil_tmp104 = (unsigned long )status;
                              if (__cil_tmp104 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            }
                            if (currentIrpStack__Parameters__DeviceIoControl__InputBufferLength < sizeof__CDROM_PLAY_AUDIO_MSF) {
                              status = -1073741820;
                              goto switch_4_break;
                            }
                            {
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                            }
                            if (status >= 0) {

                            }
                            goto switch_4_break;
                            switch_4_exp_13: 
                            Irp__IoStatus__Information = 0;
                            if (currentIrpStack__Parameters__DeviceIoControl__InputBufferLength < sizeof__CDROM_SEEK_AUDIO_MSF) {
                              status = -1073741820;
                              goto switch_4_break;
                            }
                            {
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                            }
                            if (status < 0) {
                              {
                              __cil_tmp105 = (unsigned long )status;
                              if (__cil_tmp105 == -1073741808) {
                                status = -1073741803;
                              }
                              }
                            }
                            goto switch_4_break;
                            switch_4_exp_14: 
                            Irp__IoStatus__Information = 0;
                            if (SubQPtr == 0) {
                              status = -1073741670;
                              {
                              __cil_tmp106 = (unsigned long )status;
                              if (__cil_tmp106 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            if (deviceExtension__Paused == 1) {
                              status = 0;
                              {
                              __cil_tmp107 = (unsigned long )status;
                              if (__cil_tmp107 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            {
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, SubQPtr,
                                                        sizeof__SUB_Q_CHANNEL_DATA);
                            }
                            {
                            if (status < 0) {
                              {
                              __cil_tmp109 = (unsigned long )status;
                              if (__cil_tmp109 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            }
                            {
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                            }
                            {
                            if (status < 0) {
                              {
                              __cil_tmp111 = (unsigned long )status;
                              if (__cil_tmp111 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            }
                            goto switch_4_break;
                            switch_4_exp_15: 
                            Irp__IoStatus__Information = 0;
                            if (deviceExtension__Paused == 0) {
                              status = -1073741823;
                              {
                              __cil_tmp112 = (unsigned long )status;
                              if (__cil_tmp112 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            {
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                            }
                            if (status >= 0) {
                              deviceExtension__PlayActive = 1;
                              deviceExtension__Paused = 0;
                            }
                            goto switch_4_break;
                            switch_4_exp_16: ;
                            if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength < sizeof__SUB_Q_CURRENT_POSITION) {
                              status = -1073741789;
                              Irp__IoStatus__Information = 0;
                              goto switch_4_break;
                            }
                            if (SubQPtr___0 == 0) {
                              status = -1073741670;
                              Irp__IoStatus__Information = 0;
                              {
                              __cil_tmp113 = (unsigned long )status;
                              if (__cil_tmp113 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            if (userPtr__Format != 1) {
                              status = -1073741823;
                              Irp__IoStatus__Information = 0;
                              {
                              __cil_tmp114 = (unsigned long )status;
                              if (__cil_tmp114 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            }
                            {
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, SubQPtr___0,
                                                        sizeof__SUB_Q_CHANNEL_DATA);
                            }
                            if (status >= 0) {
                              if (deviceExtension__Paused == 1) {
                                deviceExtension__PlayActive = 0;
                              }
                              Irp__IoStatus__Information = sizeof__SUB_Q_CURRENT_POSITION;
                            } else {
                              Irp__IoStatus__Information = 0;
                            }
                            goto switch_4_break;
                            switch_4_exp_17: 
                            {
                            Irp__IoStatus__Information = 0;
                            srb__CdbLength = 10;
                            srb__TimeOutValue = 10;
                            status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
                            }
                            goto switch_4_break;
                            switch_4_exp_18: ;
                            switch_4_exp_19: ;
                            switch_4_exp_20: 
                            Irp__IoStatus__Information = 0;
                            status = -1073741808;
                            goto switch_4_break;
                            switch_4_exp_21: 
                            {
                            tmp___1 = CdAudioIsPlayActive(DeviceObject);
                            }
                            if (tmp___1 == 1) {
                              deviceExtension__PlayActive = 1;
                              status = 0;
                              Irp__IoStatus__Information = 0;
                              {
                              __cil_tmp115 = (unsigned long )status;
                              if (__cil_tmp115 == -2147483626) {
                                Irp__IoStatus__Information = 0;
                              }
                              }
                              {
                              myStatus = status;
                              IofCompleteRequest(Irp, 0);
                              }
                              return (status);
                            } else {
                              {
                              deviceExtension__PlayActive = 0;
                              tmp___0 = CdAudioSendToNextDriver(DeviceObject, Irp);
                              }
                              return (tmp___0);
                            }
                            goto switch_4_break;
                            switch_4_default: 
                            {
                            tmp___2 = CdAudioSendToNextDriver(DeviceObject, Irp);
                            }
                            return (tmp___2);
                            goto switch_4_break;
                          } else {
                            switch_4_break: ;
                          }
                        }
                        }
                      }
                      }
                    }
                    }
                  }
                  }
                }
                }
              }
              }
            }
            }
          }
          }
        }
        }
      }
      }
    }
    }
  }
  }
  {
  __cil_tmp116 = (unsigned long )status;
  if (__cil_tmp116 == -2147483626) {
    Irp__IoStatus__Information = 0;
  }
  }
  {
  myStatus = status;
  IofCompleteRequest(Irp, 0);
  }
  return (status);
}
}
int CdAudioAtapiDeviceControl(int DeviceObject , int Irp ) 
{ int currentIrpStack__Parameters__DeviceIoControl__IoControlCode = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information ;
  int deviceExtension__PlayActive ;
  int srb__CdbLength ;
  int srb__TimeOutValue ;
  int Irp__IoStatus__Status ;
  int status ;
  int deviceExtension = __VERIFIER_nondet_int() ;
  int srb = __VERIFIER_nondet_int() ;
  int tmp ;
  int __cil_tmp13 ;
  int __cil_tmp14 ;
  int __cil_tmp15 ;
  int __cil_tmp16 ;
  int __cil_tmp17 ;
  int __cil_tmp18 ;

  {
  {
  __cil_tmp13 = 8;
  __cil_tmp14 = 16384;
  __cil_tmp15 = 131072;
  __cil_tmp16 = 147456;
  __cil_tmp17 = 147464;
  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp17) {
    {
    Irp__IoStatus__Information = 0;
    deviceExtension__PlayActive = 0;
    srb__CdbLength = 12;
    srb__TimeOutValue = 10;
    status = SendSrbSynchronous(deviceExtension, srb, 0, 0);
    }
    {
    if (status < 0) {
      {
      Irp__IoStatus__Status = status;
      myStatus = status;
      IofCompleteRequest(Irp, 0);
      }
      return (status);
    }
    }
  } else {
    {
    tmp = CdAudioSendToNextDriver(DeviceObject, Irp);
    }
    return (tmp);
  }
  }
  {
  Irp__IoStatus__Status = status;
  myStatus = status;
  IofCompleteRequest(Irp, 0);
  }
  return (status);
}
}
void HpCdrProcessLastSession(int Toc ) 
{ int index = __VERIFIER_nondet_int() ;

  {
  if (index) {
    index --;
  }
  return;
}
}
int HPCdrCompletion(int DeviceObject , int Irp , int Context ) 
{ int Irp__PendingReturned = __VERIFIER_nondet_int() ;
  int Irp__AssociatedIrp__SystemBuffer = __VERIFIER_nondet_int() ;

  {
  if (Irp__PendingReturned) {
    if (pended == 0) {
      pended = 1;
    } else {
      {
      errorFn();
      }
    }
  }
  if (myStatus >= 0) {
    {
    HpCdrProcessLastSession(Irp__AssociatedIrp__SystemBuffer);
    }
  }
  return (myStatus);
}
}
int CdAudioHPCdrDeviceControl(int DeviceObject , int Irp ) 
{ int currentIrpStack__Parameters__DeviceIoControl__IoControlCode = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int irpSp__Control ;
  int tmp ;
  int tmp___0 ;
  int __cil_tmp8 ;
  int __cil_tmp9 ;
  int __cil_tmp10 ;
  int __cil_tmp11 ;
  int __cil_tmp12 ;

  {
  {
  __cil_tmp8 = 56;
  __cil_tmp9 = 16384;
  __cil_tmp10 = 131072;
  __cil_tmp11 = 147456;
  __cil_tmp12 = 147512;
  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp12) {
    if (s != NP) {
      {
      errorFn();
      }
    } else {
      if (compRegistered != 0) {
        {
        errorFn();
        }
      } else {
        compRegistered = 1;
        routine = 0;
      }
    }
    {
    irpSp__Control = 224;
    tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
    }
    return (tmp);
  } else {
    {
    tmp___0 = CdAudioSendToNextDriver(DeviceObject, Irp);
    }
    return (tmp___0);
  }
  }
  return (-1073741823);
}
}
int CdAudioForwardIrpSynchronous(int DeviceObject , int Irp ) 
{ int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int event = __VERIFIER_nondet_int() ;
  int status ;
  int irpSp__Control ;

  {
  if (s != NP) {
    {
    errorFn();
    }
  } else {
    if (compRegistered != 0) {
      {
      errorFn();
      }
    } else {
      compRegistered = 1;
      routine = 1;
    }
  }
  {
  irpSp__Control = 224;
  status = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  status = 259;
  }
  if (status) {
    {
    KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
    status = myStatus;
    }
  }
  return (status);
}
}
void CdAudioUnload(int DriverObject ) 
{ 

  {
  return;
}
}
int CdAudioPower(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int tmp ;

  {
  if (s == NP) {
    s = SKIP1;
  } else {
    {
    errorFn();
    }
  }
  {
  Irp__CurrentLocation ++;
  Irp__Tail__Overlay__CurrentStackLocation ++;
  tmp = PoCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
  return (tmp);
}
}
void stub_driver_init(void) 
{ 

  {
  s = NP;
  customIrp = 0;
  setEventCalled = customIrp;
  lowerDriverReturn = setEventCalled;
  compRegistered = lowerDriverReturn;
  compFptr = compRegistered;
  pended = compFptr;
  return;
}
}
int main(void) 
{ int pirp__IoStatus__Status ;
  int d = __VERIFIER_nondet_int() ;
  int status = __VERIFIER_nondet_int() ;
  int irp = __VERIFIER_nondet_int() ;
  int we_should_unload = __VERIFIER_nondet_int() ;
  int irp_choice = __VERIFIER_nondet_int() ;
  int devobj = __VERIFIER_nondet_int() ;
  int __cil_tmp9 ;

  {
  {

 s  = 0;
 UNLOADED  = 0;
 NP  = 0;
 DC  = 0;
 SKIP1  = 0;
 SKIP2  = 0;
 MPR1  = 0;
 MPR3  = 0;
 IPC  = 0;
 pended  = 0;
 compFptr  = 0;
 compRegistered  = 0;
 lowerDriverReturn  = 0;
 setEventCalled  = 0;
 customIrp  = 0;
 routine  = 0;
 myStatus  = 0;
 pirp  = 0;
 Executive  = 0;
 Suspended  =    5;
 KernelMode  =    0;
 DeviceUsageTypePaging  =    1;


  pirp = irp;
  _BLAST_init();
  }
  if (status >= 0) {
    s = NP;
    customIrp = 0;
    setEventCalled = customIrp;
    lowerDriverReturn = setEventCalled;
    compRegistered = lowerDriverReturn;
    compFptr = compRegistered;
    pended = compFptr;
    pirp__IoStatus__Status = 0;
    myStatus = 0;
    if (irp_choice == 0) {
      pirp__IoStatus__Status = -1073741637;
      myStatus = -1073741637;
    }
    {
    stub_driver_init();
    }
    {
    if (status < 0) {
      return (-1);
    }
    }
    int tmp_ndt_1;
    tmp_ndt_1 = __VERIFIER_nondet_int();
    if (tmp_ndt_1 == 2) {
      goto switch_5_2;
    } else {
      int tmp_ndt_2;
      tmp_ndt_2 = __VERIFIER_nondet_int();
      if (tmp_ndt_2 == 3) {
        goto switch_5_3;
      } else {
        int tmp_ndt_3;
	tmp_ndt_3 = __VERIFIER_nondet_int();
        if (tmp_ndt_3 == 4) {
          goto switch_5_4;
        } else {
          goto switch_5_default;
          if (0) {
            switch_5_2: 
            {
            status = CdAudioDeviceControl(devobj, pirp);
            }
            goto switch_5_break;
            switch_5_3: 
            {
            status = CdAudioPnp(devobj, pirp);
            }
            goto switch_5_break;
            switch_5_4: 
            {
            status = CdAudioPower(devobj, pirp);
            }
            goto switch_5_break;
            switch_5_default: ;
            return (-1);
          } else {
            switch_5_break: ;
          }
        }
      }
    }
    if (we_should_unload) {
      {
      CdAudioUnload(d);
      }
    }
  }
  if (pended == 1) {
    if (s == NP) {
      s = NP;
    } else {
      goto _L___2;
    }
  } else {
    _L___2: 
    if (pended == 1) {
      if (s == MPR3) {
        s = MPR3;
      } else {
        goto _L___1;
      }
    } else {
      _L___1: 
      if (s != UNLOADED) {
        if (status != -1) {
          if (s != SKIP2) {
            if (s != IPC) {
              if (s != DC) {
                {
                errorFn();
                }
              } else {
                goto _L___0;
              }
            } else {
              goto _L___0;
            }
          } else {
            _L___0: 
            if (pended != 1) {
              if (s == DC) {
                if (status == 259) {
                  {
                  errorFn();
                  }
                }
              } else {
                if (status != lowerDriverReturn) {
                  {
                  errorFn();
                  }
                }
              }
            }
          }
        }
      }
    }
  }
  return (status);
}
}
void stubMoreProcessingRequired(void) 
{ 

  {
  if (s == NP) {
    s = MPR1;
  } else {
    {
    errorFn();
    }
  }
  return;
}
}
int IofCallDriver(int DeviceObject , int Irp ) 
{ int Irp__PendingReturned = __VERIFIER_nondet_int() ;
  int returnVal2 ;
  int compRetStatus ;
  int lcontext = __VERIFIER_nondet_int() ;
  unsigned long __cil_tmp8 ;

  {
  if (compRegistered) {
    if (routine == 0) {
      {
      compRetStatus = HPCdrCompletion(DeviceObject, Irp, lcontext);
      }
    } else {
      if (routine == 1) {
        {
        compRetStatus = CdAudioSignalCompletion(DeviceObject, Irp, lcontext);
        }
      }
    }
    {
    __cil_tmp8 = (unsigned long )compRetStatus;
    if (__cil_tmp8 == -1073741802) {
      {
      stubMoreProcessingRequired();
      }
    }
    }
  }
  if (Irp__PendingReturned) {
    returnVal2 = 259;
  } else {
    int tmp_ndt_5;
    tmp_ndt_5 = __VERIFIER_nondet_int();
    if (tmp_ndt_5 == 0) {
      goto switch_6_0;
    } else {
      int tmp_ndt_6;
      tmp_ndt_6 = __VERIFIER_nondet_int();
      if (tmp_ndt_6 == 1) {
        goto switch_6_1;
      } else {
        goto switch_6_default;
        if (0) {
          switch_6_0: 
          returnVal2 = 0;
          goto switch_6_break;
          switch_6_1: 
          returnVal2 = -1073741823;
          goto switch_6_break;
          switch_6_default: 
          returnVal2 = 259;
          goto switch_6_break;
        } else {
          switch_6_break: ;
        }
      }
    }
  }
  if (s == NP) {
    s = IPC;
    lowerDriverReturn = returnVal2;
  } else {
    if (s == MPR1) {
      if (returnVal2 == 259) {
        s = MPR3;
        lowerDriverReturn = returnVal2;
      } else {
        s = NP;
        lowerDriverReturn = returnVal2;
      }
    } else {
      if (s == SKIP1) {
        s = SKIP2;
        lowerDriverReturn = returnVal2;
      } else {
        {
        errorFn();
        }
      }
    }
  }
  return (returnVal2);
}
}
void IofCompleteRequest(int Irp , int PriorityBoost ) 
{ 

  {
  if (s == NP) {
    s = DC;
  } else {
    {
    errorFn();
    }
  }
  return;
}
}
int KeSetEvent(int Event , int Increment , int Wait ) 
{ int l = __VERIFIER_nondet_int() ;

  {
  setEventCalled = 1;
  return (l);
}
}
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable ,
                          int Timeout ) 
{

  {
  if (s == MPR3) {
    if (setEventCalled == 1) {
      s = NP;
      setEventCalled = 0;
    } else {
      goto _L;
    }
  } else {
    _L: 
    if (customIrp == 1) {
      s = NP;
      customIrp = 0;
    } else {
      if (s == MPR3) {
        {
        errorFn();
        }
      }
    }
  }
  int tmp_ndt_7; 
  tmp_ndt_7 = __VERIFIER_nondet_int();
  if (tmp_ndt_7 == 0) {
    goto switch_7_0;
  } else {
    goto switch_7_default;
    if (0) {
      switch_7_0: ;
      return (0);
      switch_7_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
int PoCallDriver(int DeviceObject , int Irp ) 
{
  int compRetStatus ;
  int returnVal ;
  int lcontext = __VERIFIER_nondet_int() ;
  unsigned long __cil_tmp7 ;
  long __cil_tmp8 ;

  {
  if (compRegistered) {
    if (routine == 0) {
      {
      compRetStatus = HPCdrCompletion(DeviceObject, Irp, lcontext);
      }
    } else {
      if (routine == 1) {
        {
        compRetStatus = CdAudioSignalCompletion(DeviceObject, Irp, lcontext);
        }
      }
    }
    {
    __cil_tmp7 = (unsigned long )compRetStatus;
    if (__cil_tmp7 == -1073741802) {
      {
      stubMoreProcessingRequired();
      }
    }
    }
  }
  int tmp_ndt_8; 
  tmp_ndt_8 = __VERIFIER_nondet_int();
  if (tmp_ndt_8 == 0) {
    goto switch_8_0;
  } else {
    int tmp_ndt_9; 
    tmp_ndt_9 = __VERIFIER_nondet_int();
    if (tmp_ndt_9 == 1) {
      goto switch_8_1;
    } else {
      goto switch_8_default;
      if (0) {
        switch_8_0: 
        returnVal = 0;
        goto switch_8_break;
        switch_8_1: 
        returnVal = -1073741823;
        goto switch_8_break;
        switch_8_default: 
        returnVal = 259;
        goto switch_8_break;
      } else {
        switch_8_break: ;
      }
    }
  }
  if (s == NP) {
    s = IPC;
    lowerDriverReturn = returnVal;
  } else {
    if (s == MPR1) {
      {
      __cil_tmp8 = (long )returnVal;
      if (__cil_tmp8 == 259L) {
        s = MPR3;
        lowerDriverReturn = returnVal;
      } else {
        s = NP;
        lowerDriverReturn = returnVal;
      }
      }
    } else {
      if (s == SKIP1) {
        s = SKIP2;
        lowerDriverReturn = returnVal;
      } else {
        {
        errorFn();
        }
      }
    }
  }
  return (returnVal);
}
}
int ZwClose(int Handle ) 
{

  {
  int tmp_ndt_10; 
  tmp_ndt_10 = __VERIFIER_nondet_int();
  if (tmp_ndt_10 == 0) {
    goto switch_9_0;
  } else {
    goto switch_9_default;
    if (0) {
      switch_9_0: ;
      return (0);
      switch_9_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
