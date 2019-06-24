// RUN: %sea bpf -O3 --bmc=mono --bound=5  --horn-stats --inline  "%s"  2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-bmc-crab=false  --bmc=path --horn-bmc-muc=assume --bound=5  --horn-stats --inline  "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-bmc-crab=false  --bmc=path --horn-bmc-muc=quickXplain --bound=5  --horn-stats --inline --dsa=llvm "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-bmc-crab=true  --bmc=path --bound=5  --horn-stats --inline   "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-gsa --bmc=mono --bound=5  --horn-stats --inline --dsa=llvm "%s"  2>&1 | OutputCheck %s
// CHECK: ^unsat$

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);

int DiskPerfDispatchPnp(int DeviceObject , int Irp );
int DiskPerfIrpCompletion(int DeviceObject , int Irp , int Context );
int DiskPerfStartDevice(int DeviceObject , int Irp );
int DiskPerfRemoveDevice(int DeviceObject , int Irp );
int DiskPerfSendToNextDriver(int DeviceObject , int Irp );
int DiskPerfDispatchPower(int DeviceObject , int Irp );
int DiskPerfForwardIrpSynchronous(int DeviceObject , int Irp );
int DiskPerfCreate(int DeviceObject , int Irp );
int DiskPerfIoCompletion(int DeviceObject , int Irp , int Context );
int DiskPerfDeviceControl(int DeviceObject , int Irp );
int DiskPerfShutdownFlush(int DeviceObject , int Irp );
int DiskPerfRegisterDevice(int DeviceObject );
int IoBuildDeviceIoControlRequest(int IoControlCode , int DeviceObject , int InputBuffer ,
                                  int InputBufferLength , int OutputBuffer , int OutputBufferLength ,
                                  int InternalDeviceIoControl , int Event , int IoStatusBlock );
int IofCallDriver(int DeviceObject , int Irp );
int KeSetEvent(int Event , int Increment , int Wait );
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable ,
                          int Timeout );
int PoCallDriver(int DeviceObject , int Irp );
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
int myStatus  ;
int routine  ;
int pirp  ;
int Executive ;
int KernelMode ;

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
void DiskPerfSyncFilterWithTarget(int FilterDevice , int TargetDevice ) 
{ int FilterDevice__Flags ;
  int TargetDevice__Characteristics ;
  int FilterDevice__Characteristics ;
  int propFlags ;

  {
  //propFlags = 0;
  //FilterDevice__Flags |= propFlags;
  //propFlags = TargetDevice__Characteristics & 7;
  //FilterDevice__Characteristics |= propFlags;
  return;
}
}
int DiskPerfDispatchPnp(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int irpSp__MinorFunction = __VERIFIER_nondet_int() ;
  int irpSp ;
  int status ;
  int tmp ;

  {
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
  if (irpSp__MinorFunction == 0) {
    goto switch_0_0;
  } else {
    if (irpSp__MinorFunction == 2) {
      goto switch_0_2;
    } else {
      goto switch_0_default;
      if (0) {
        switch_0_0: 
        {
        status = DiskPerfStartDevice(DeviceObject, Irp);
        }
        goto switch_0_break;
        switch_0_2: 
        {
        status = DiskPerfRemoveDevice(DeviceObject, Irp);
        }
        goto switch_0_break;
        switch_0_default: 
        {
        tmp = DiskPerfSendToNextDriver(DeviceObject, Irp);
        }
        return (tmp);
      } else {
        switch_0_break: ;
      }
    }
  }
  return (status);
}
}
int DiskPerfIrpCompletion(int DeviceObject , int Irp , int Context ) 
{ int Event ;

  {
  {
  Event = Context;
  KeSetEvent(Event, 0, 0);
  }
  return (-1073741802);
}
}
int DiskPerfStartDevice(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int deviceExtension ;
  int status ;

  {
  {
  deviceExtension = DeviceObject__DeviceExtension;
  status = DiskPerfForwardIrpSynchronous(DeviceObject, Irp);
  DiskPerfSyncFilterWithTarget(DeviceObject, deviceExtension__TargetDeviceObject);
  DiskPerfRegisterDevice(DeviceObject);
  Irp__IoStatus__Status = status;
  myStatus = status;
  IofCompleteRequest(Irp, 0);
  }
  return (status);
}
}
int DiskPerfRemoveDevice(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__WmilibContext = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int status ;
  int deviceExtension ;
  int wmilibContext ;

  {
  {
  deviceExtension = DeviceObject__DeviceExtension;
  wmilibContext = deviceExtension__WmilibContext;
  status = DiskPerfForwardIrpSynchronous(DeviceObject, Irp);
  Irp__IoStatus__Status = status;
  myStatus = status;
  IofCompleteRequest(Irp, 0);
  }
  return (status);
}
}
int DiskPerfSendToNextDriver(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int deviceExtension ;
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
  deviceExtension = DeviceObject__DeviceExtension;
  tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
  return (tmp);
}
}
int DiskPerfDispatchPower(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int deviceExtension ;
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
  deviceExtension = DeviceObject__DeviceExtension;
  tmp = PoCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
  return (tmp);
}
}
int DiskPerfForwardIrpSynchronous(int DeviceObject , int Irp ) 
{ int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int deviceExtension ;
  int event = __VERIFIER_nondet_int() ;
  int status ;
  int nextIrpSp__Control ;
  int irpSp ;
  int nextIrpSp ;
  int irpSp__Context ;
  int irpSp__Control ;
  int irpSp___0 ;
  long __cil_tmp15 ;

  {
  deviceExtension = DeviceObject__DeviceExtension;
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
  nextIrpSp = Irp__Tail__Overlay__CurrentStackLocation - 1;
  nextIrpSp__Control = 0;
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
  irpSp___0 = Irp__Tail__Overlay__CurrentStackLocation - 1;
  irpSp__Context = event;
  irpSp__Control = 224;
  status = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
  {
  __cil_tmp15 = (long )status;
  if (__cil_tmp15 == 259L) {
    {
    KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
    status = myStatus;
    }
  }
  }
  return (status);
}
}
int DiskPerfCreate(int DeviceObject , int Irp ) 
{ 

  {
  {
  myStatus = 0;
  IofCompleteRequest(Irp, 0);
  }
  return (0);
}
}
int DiskPerfIoCompletion(int DeviceObject , int Irp , int Context ) 
{ int irpStack__MajorFunction = __VERIFIER_nondet_int() ;
  int partitionCounters__BytesRead__QuadPart = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information = __VERIFIER_nondet_int() ;
  int partitionCounters__ReadCount = __VERIFIER_nondet_int() ;
  int partitionCounters__ReadTime__QuadPart = __VERIFIER_nondet_int() ;
  int difference__QuadPart = __VERIFIER_nondet_int() ;
  int partitionCounters__BytesWritten__QuadPart = __VERIFIER_nondet_int() ;
  int partitionCounters__WriteCount = __VERIFIER_nondet_int() ;
  int partitionCounters__WriteTime__QuadPart = __VERIFIER_nondet_int() ;
  int Irp__Flags = __VERIFIER_nondet_int() ;
  int partitionCounters__SplitCount = __VERIFIER_nondet_int() ;
  int Irp__PendingReturned = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation__Control ;
  int partitionCounters = __VERIFIER_nondet_int() ;
  int queueLen = __VERIFIER_nondet_int() ;

  {
  if (partitionCounters == 0) {
    return (0);
  }
  if (queueLen < 0) {

  }
  if (queueLen == 0) {

  }
  if (irpStack__MajorFunction == 3) {
    partitionCounters__BytesRead__QuadPart += Irp__IoStatus__Information;
    partitionCounters__ReadCount ++;
    partitionCounters__ReadTime__QuadPart += difference__QuadPart;
  } else {
    partitionCounters__BytesWritten__QuadPart += Irp__IoStatus__Information;
    partitionCounters__WriteCount ++;
    partitionCounters__WriteTime__QuadPart += difference__QuadPart;
  }
  if (Irp__Flags != 8) {
    partitionCounters__SplitCount ++;
  }
  else {
  }
  if (Irp__PendingReturned) {
    if (pended == 0) {
      pended = 1;
    } else {
      {
      errorFn();
      }
    }
    //Irp__Tail__Overlay__CurrentStackLocation__Control |= 1;
  }
  return (0);
}
}
int DiskPerfDeviceControl(int DeviceObject , int Irp ) 
{ int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int currentIrpStack__Parameters__DeviceIoControl__IoControlCode = __VERIFIER_nondet_int() ;
  int currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength = __VERIFIER_nondet_int() ;
  int sizeof__DISK_PERFORMANCE = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information ;
  int deviceExtension__DiskCounters = __VERIFIER_nondet_int() ;
  int Irp__AssociatedIrp__SystemBuffer = __VERIFIER_nondet_int() ;
  int deviceExtension__Processors = __VERIFIER_nondet_int() ;
  int totalCounters__QueueDepth ;
  int deviceExtension__QueueDepth = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int deviceExtension ;
  int currentIrpStack ;
  int status ;
  int i ;
  int totalCounters ;
  int diskCounters ;
  int tmp ;
  int __cil_tmp24 ;
  int __cil_tmp25 ;
  int __cil_tmp26 ;

  {
  deviceExtension = DeviceObject__DeviceExtension;
  currentIrpStack = Irp__Tail__Overlay__CurrentStackLocation;
  {
  __cil_tmp24 = 32;
  __cil_tmp25 = 458752;
  __cil_tmp26 = 458784;
  if (currentIrpStack__Parameters__DeviceIoControl__IoControlCode == __cil_tmp26) {
    if (currentIrpStack__Parameters__DeviceIoControl__OutputBufferLength < sizeof__DISK_PERFORMANCE) {
      status = -1073741789;
      Irp__IoStatus__Information = 0;
    } else {
      diskCounters = deviceExtension__DiskCounters;
      if (diskCounters == 0) {
        {
        Irp__IoStatus__Status = -1073741823;
        myStatus = -1073741823;
        IofCompleteRequest(Irp, 0);
        }
        return (-1073741823);
      }
      totalCounters = Irp__AssociatedIrp__SystemBuffer;
      i = 0;
      {
      while (1) {
        while_0_continue: /* CIL Label */ ;

        if (i >= deviceExtension__Processors) {
          goto while_1_break;
        }
        i ++;
      }
      while_0_break: /* CIL Label */ ;
      }
      while_1_break: 
      totalCounters__QueueDepth = deviceExtension__QueueDepth;
      status = 0;
      Irp__IoStatus__Information = sizeof__DISK_PERFORMANCE;
    }
    {
    Irp__IoStatus__Status = status;
    myStatus = status;
    IofCompleteRequest(Irp, 0);
    }
    return (status);
  } else {
    {
    Irp__CurrentLocation ++;
    Irp__Tail__Overlay__CurrentStackLocation ++;
    tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
    }
    return (tmp);
  }
  }
}
}
int DiskPerfShutdownFlush(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int deviceExtension ;
  int tmp ;

  {
  {
  deviceExtension = DeviceObject__DeviceExtension;
  Irp__CurrentLocation ++;
  Irp__Tail__Overlay__CurrentStackLocation ++;
  tmp = IofCallDriver(deviceExtension__TargetDeviceObject, Irp);
  }
  return (tmp);
}
}
void DiskPerfUnload(int DriverObject ) 
{ 

  {
  return;
}
}
int DiskPerfRegisterDevice(int DeviceObject ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int deviceExtension__TargetDeviceObject = __VERIFIER_nondet_int() ;
  int sizeof__number = __VERIFIER_nondet_int() ;
  int ioStatus__Status = __VERIFIER_nondet_int() ;
  int sizeof__VOLUME_NUMBER = __VERIFIER_nondet_int() ;
  int volumeNumber__VolumeManagerName__0 = __VERIFIER_nondet_int() ;
  int status ;
  int ioStatus = __VERIFIER_nondet_int() ;
  int event = __VERIFIER_nondet_int() ;
  int deviceExtension ;
  int irp ;
  int number = __VERIFIER_nondet_int() ;
  int registrationFlag ;
  int sizeof__MOUNTDEV_NAME = __VERIFIER_nondet_int() ;
  int output__NameLength = __VERIFIER_nondet_int() ;
  int outputSize ;
  int output = __VERIFIER_nondet_int() ;
  int volumeNumber = __VERIFIER_nondet_int() ;
  int __cil_tmp20 ;
  int __cil_tmp21 ;
  int __cil_tmp22 ;
  long __cil_tmp23 ;
  int __cil_tmp24 ;
  int __cil_tmp25 ;
  int __cil_tmp26 ;
  long __cil_tmp27 ;
  unsigned long __cil_tmp28 ;
  int __cil_tmp29 ;
  int __cil_tmp30 ;
  int __cil_tmp31 ;
  long __cil_tmp32 ;
  int __cil_tmp33 ;
  int __cil_tmp34 ;
  int __cil_tmp35 ;
  int __cil_tmp36 ;
  long __cil_tmp37 ;
  int __cil_tmp38 ;
  int __cil_tmp39 ;

  {
  {
  registrationFlag = 0;
  deviceExtension = DeviceObject__DeviceExtension;
  __cil_tmp20 = 4224;
  __cil_tmp21 = 2949120;
  __cil_tmp22 = 2953344;
  irp = IoBuildDeviceIoControlRequest(__cil_tmp22, deviceExtension__TargetDeviceObject,
                                      0, 0, number, sizeof__number, 0, event, ioStatus);
  }
  if (! irp) {
    return (-1073741670);
  }
  {
  status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
  }
  {
  __cil_tmp23 = (long )status;
  if (__cil_tmp23 == 259L) {
    {
    KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
    status = ioStatus__Status;
    }
  }
  }
  if (status < 0) {
    outputSize = sizeof__MOUNTDEV_NAME;
    if (! output) {
      return (-1073741670);
    }
    {
    __cil_tmp24 = 8;
    __cil_tmp25 = 5046272;
    __cil_tmp26 = 5046280;
    irp = IoBuildDeviceIoControlRequest(__cil_tmp26, deviceExtension__TargetDeviceObject,
                                        0, 0, output, outputSize, 0, event, ioStatus);
    }
    if (! irp) {
      return (-1073741670);
    }
    {
    status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
    }
    {
    __cil_tmp27 = (long )status;
    if (__cil_tmp27 == 259L) {
      {
      KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
      status = ioStatus__Status;
      }
    }
    }
    {
    __cil_tmp28 = (unsigned long )status;
    if (__cil_tmp28 == -2147483643) {
      outputSize = sizeof__MOUNTDEV_NAME + output__NameLength;
      if (! output) {
        return (-1073741670);
      }
      {
      __cil_tmp29 = 8;
      __cil_tmp30 = 5046272;
      __cil_tmp31 = 5046280;
      irp = IoBuildDeviceIoControlRequest(__cil_tmp31, deviceExtension__TargetDeviceObject,
                                          0, 0, output, outputSize, 0, event, ioStatus);
      }
      if (! irp) {
        return (-1073741670);
      }
      {
      status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
      }
      {
      __cil_tmp32 = (long )status;
      if (__cil_tmp32 == 259L) {
        {
        KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
        status = ioStatus__Status;
        }
      }
      }
    }
    }
    {
    if (status < 0) {
      return (status);
    }
    }
    {
    __cil_tmp34 = 28;
    __cil_tmp35 = 5636096;
    __cil_tmp36 = 5636124;
    irp = IoBuildDeviceIoControlRequest(__cil_tmp36, deviceExtension__TargetDeviceObject,
                                        0, 0, volumeNumber, sizeof__VOLUME_NUMBER,
                                        0, event, ioStatus);
    }
    if (! irp) {
      return (-1073741670);
    }
    {
    status = IofCallDriver(deviceExtension__TargetDeviceObject, irp);
    }
    {
    __cil_tmp37 = (long )status;
    if (__cil_tmp37 == 259L) {
      {
      KeWaitForSingleObject(event, Executive, KernelMode, 0, 0);
      status = ioStatus__Status;
      }
    }
    }
    {
    if (status < 0) {
      goto _L;
    } else {
      if (volumeNumber__VolumeManagerName__0 == 0) {
        _L: 
        if (status >= 0) {

        }
      }
    }
    }
  }
  {
  if (status < 0) {

  }
  }
  return (status);
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
{ int d = __VERIFIER_nondet_int() ;
  int status = __VERIFIER_nondet_int() ;
  int we_should_unload = __VERIFIER_nondet_int() ;
  int irp = __VERIFIER_nondet_int() ;
  int pirp__IoStatus__Status ;
  int irp_choice = __VERIFIER_nondet_int() ;
  int devobj = __VERIFIER_nondet_int() ;
  int __cil_tmp9 ;

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
 myStatus  = 0;
 routine  = 0;
 pirp  = 0;
 Executive  = 0;
 KernelMode  = 0;

  {
  {
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
    if (tmp_ndt_1 == 0) {
      goto switch_2_0;
    } else {
      int tmp_ndt_2;
      tmp_ndt_2 = __VERIFIER_nondet_int();
      if (tmp_ndt_2 == 2) {
        goto switch_2_2;
      } else {
        int tmp_ndt_3;
        tmp_ndt_3 = __VERIFIER_nondet_int();
        if (tmp_ndt_3 == 3) {
          goto switch_2_3;
        } else {
	  int tmp_ndt_4;
	  tmp_ndt_4 = __VERIFIER_nondet_int();
          if (tmp_ndt_4 == 4) {
            goto switch_2_4;
          } else {
	    int tmp_ndt_5;
	    tmp_ndt_5 = __VERIFIER_nondet_int();
            if (tmp_ndt_5 == 12) {
              goto switch_2_12;
            } else {
              goto switch_2_default;
              if (0) {
                switch_2_0: 
                {
                status = DiskPerfCreate(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_2: 
                {
                status = DiskPerfDeviceControl(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_3: 
                {
                status = DiskPerfDispatchPnp(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_4: 
                {
                status = DiskPerfDispatchPower(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_12: 
                {
                status = DiskPerfShutdownFlush(devobj, pirp);
                }
                goto switch_2_break;
                switch_2_default: ;
                return (-1);
              } else {
                switch_2_break: ;
              }
            }
          }
        }
      }
    }
    if (we_should_unload) {
      {
      DiskPerfUnload(d);
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
            if (pended == 1) {
              if (status != 259) {
                {
                errorFn();
                }
              }
            } else {
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
int IoBuildDeviceIoControlRequest(int IoControlCode , int DeviceObject , int InputBuffer ,
                                  int InputBufferLength , int OutputBuffer , int OutputBufferLength ,
                                  int InternalDeviceIoControl , int Event , int IoStatusBlock ) 
{
  int malloc_ret = __VERIFIER_nondet_int() ;

  {
  customIrp = 1;
  int tmp_ndt_7;
  tmp_ndt_7 = __VERIFIER_nondet_int();
  if (tmp_ndt_7 == 0) {
    goto switch_3_0;
  } else {
    goto switch_3_default;
    if (0) {
      switch_3_0: ;
      return (malloc_ret);
      switch_3_default: ;
      return (0);
    } else {

    }
  }
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
{
  int returnVal2 ;
  int compRetStatus ;
  int lcontext = __VERIFIER_nondet_int() ;
  unsigned long __cil_tmp7 ;

  {
  if (compRegistered) {
    if (routine == 0) {
      {
      compRetStatus = DiskPerfIrpCompletion(DeviceObject, Irp, lcontext);
      }
    } else {
      {
      compRetStatus = DiskPerfIoCompletion(DeviceObject, Irp, lcontext);
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
    goto switch_4_0;
  } else {
  int tmp_ndt_9;
  tmp_ndt_9 = __VERIFIER_nondet_int();
    if (tmp_ndt_9 == 1) {
      goto switch_4_1;
    } else {
      goto switch_4_default;
      if (0) {
        switch_4_0: 
        returnVal2 = 0;
        goto switch_4_break;
        switch_4_1: 
        returnVal2 = -1073741823;
        goto switch_4_break;
        switch_4_default: 
        returnVal2 = 259;
        goto switch_4_break;
      } else {
        switch_4_break: ;
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
  int tmp_ndt_10;
  tmp_ndt_10 = __VERIFIER_nondet_int();
  if (tmp_ndt_10 == 0) {
    goto switch_5_0;
  } else {
    goto switch_5_default;
    if (0) {
      switch_5_0: ;
      return (0);
      switch_5_default: ;
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
      compRetStatus = DiskPerfIrpCompletion(DeviceObject, Irp, lcontext);
      }
    } else {
      if (routine == 1) {
        {
        compRetStatus = DiskPerfIoCompletion(DeviceObject, Irp, lcontext);
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
  int tmp_ndt_11;
  tmp_ndt_11 = __VERIFIER_nondet_int();
  if (tmp_ndt_11 == 0) {
    goto switch_6_0;
  } else {
  int tmp_ndt_12;
  tmp_ndt_12 = __VERIFIER_nondet_int();
    if (tmp_ndt_12 == 1) {
      goto switch_6_1;
    } else {
      goto switch_6_default;
      if (0) {
        switch_6_0: 
        returnVal = 0;
        goto switch_6_break;
        switch_6_1: 
        returnVal = -1073741823;
        goto switch_6_break;
        switch_6_default: 
        returnVal = 259;
        goto switch_6_break;
      } else {
        switch_6_break: ;
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
