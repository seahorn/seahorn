// RUN: %sea bpf -O3 --bmc=mono --bound=5  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-bmc-crab=false --horn-bmc-crab-invariants=false --bmc=path --horn-bmc-muc=assume --bound=5  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// -- Disabled because it takes too long
// %sea bpf -O3 --horn-bmc-crab=false  --bmc=path --horn-bmc-muc=quickXplain --dsa=sea-ci --bound=5  --horn-stats --inline "%s" 2>&1 | OutputCheck %s
// RUN: %sea bpf -O3 --horn-bmc-crab=true --horn-bmc-crab-invariants=false --bmc=path --bound=5  --horn-stats --inline   "%s" 2>&1 | OutputCheck %s
// -- Disabled because it takes too long
// %sea bpf -O3 --horn-gsa --bmc=mono --bound=5  --horn-stats --inline --dsa=sea-ci "%s" 2>&1 | OutputCheck %s
// CHECK: ^sat$

extern void __VERIFIER_error() __attribute__ ((__noreturn__));

extern char __VERIFIER_nondet_char(void);
extern int __VERIFIER_nondet_int(void);
extern long __VERIFIER_nondet_long(void);
extern void *__VERIFIER_nondet_pointer(void);

int FlAcpiConfigureFloppy(int DisketteExtension , int FdcInfo );
int FlQueueIrpToThread(int Irp , int DisketteExtension );
int FloppyPnp(int DeviceObject , int Irp );
int FloppyStartDevice(int DeviceObject , int Irp );
int FloppyPnpComplete(int DeviceObject , int Irp , int Context );
int FlFdcDeviceIo(int DeviceObject , int Ioctl , int Data );
int IoBuildDeviceIoControlRequest(int IoControlCode , int DeviceObject , int InputBuffer ,
                                  int InputBufferLength , int OutputBuffer , int OutputBufferLength ,
                                  int InternalDeviceIoControl , int Event , int IoStatusBlock );
int IoDeleteSymbolicLink(int SymbolicLinkName );
int IoQueryDeviceDescription(int BusType , int BusNumber , int ControllerType , int ControllerNumber ,
                             int PeripheralType , int PeripheralNumber , int CalloutRoutine ,
                             int Context );
int IoRegisterDeviceInterface(int PhysicalDeviceObject , int InterfaceClassGuid ,
                              int ReferenceString , int SymbolicLinkName );
int IoSetDeviceInterfaceState(int SymbolicLinkName , int Enable );
int IofCallDriver(int DeviceObject , int Irp );
int KeSetEvent(int Event , int Increment , int Wait );
int KeWaitForSingleObject(int Object , int WaitReason , int WaitMode , int Alertable ,
                          int Timeout );
int ObReferenceObjectByHandle(int Handle , int DesiredAccess , int ObjectType , int AccessMode ,
                              int Object , int HandleInformation );
int PsCreateSystemThread(int ThreadHandle , int DesiredAccess , int ObjectAttributes ,
                         int ProcessHandle , int ClientId , int StartRoutine , int StartContext );
int ZwClose(int Handle );
void IofCompleteRequest(int Irp , int PriorityBoost );
extern int __VERIFIER_nondet_int();
int FloppyThread  ;
int KernelMode  ;
int Suspended  ;
int Executive  ;
int DiskController  ;
int FloppyDiskPeripheral  ;
int FlConfigCallBack  ;
int MaximumInterfaceType  ;
int MOUNTDEV_MOUNTED_DEVICE_GUID  ;
int myStatus  ;
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
int compRegistered  ;
int lowerDriverReturn  ;
int setEventCalled  ;
int customIrp  ;

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
  compRegistered = 0;
  lowerDriverReturn = 0;
  setEventCalled = 0;
  customIrp = 0;
  return;
}
}
int PagingReferenceCount  =    0;
int PagingMutex  =    0;
int FlAcpiConfigureFloppy(int DisketteExtension , int FdcInfo ) 
{ 

  {
  return (0);
}
}
int FlQueueIrpToThread(int Irp , int DisketteExtension ) 
{ int status ;
  int threadHandle = __VERIFIER_nondet_int() ;
  int DisketteExtension__PoweringDown = __VERIFIER_nondet_int() ;
  int DisketteExtension__ThreadReferenceCount = __VERIFIER_nondet_int() ;
  int DisketteExtension__FloppyThread = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int Irp__IoStatus__Information ;
  int Irp__Tail__Overlay__CurrentStackLocation__Control ;
  int ObjAttributes = __VERIFIER_nondet_int() ;
  int __cil_tmp12 ;
  int __cil_tmp13 ;

  {
  if (DisketteExtension__PoweringDown == 1) {
    myStatus = -1073741101;
    Irp__IoStatus__Status = -1073741101;
    Irp__IoStatus__Information = 0;
    return (-1073741101);
  }
  DisketteExtension__ThreadReferenceCount ++;
  if (DisketteExtension__ThreadReferenceCount == 0) {
    DisketteExtension__ThreadReferenceCount ++;
    PagingReferenceCount ++;
    if (PagingReferenceCount == 1) {

    }
    {
    status = PsCreateSystemThread(threadHandle, 0, ObjAttributes, 0, 0, FloppyThread,
                                  DisketteExtension);
    }
    {
    if (status < 0) {
      DisketteExtension__ThreadReferenceCount = -1;
      PagingReferenceCount --;
      if (PagingReferenceCount == 0) {

      }
      return (status);
    }
    }
    {
    status = ObReferenceObjectByHandle(threadHandle, 1048576, 0, KernelMode, DisketteExtension__FloppyThread,
                                       0);
    ZwClose(threadHandle);
    }
    {
    if (status < 0) {
      return (status);
    }
    }
  }
 // Irp__Tail__Overlay__CurrentStackLocation__Control |= 1;
  if (pended == 0) {
    pended = 1;
  } else {
    {
    errorFn();
    }
  }
  return (259);
}
}
int FloppyPnp(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Information ;
  int Irp__IoStatus__Status ;
  int Irp__CurrentLocation = __VERIFIER_nondet_int() ;
  int disketteExtension__IsRemoved = __VERIFIER_nondet_int() ;
  int disketteExtension__IsStarted = __VERIFIER_nondet_int() ;
  int disketteExtension__TargetObject = __VERIFIER_nondet_int() ;
  int disketteExtension__HoldNewRequests ;
  int disketteExtension__FloppyThread = __VERIFIER_nondet_int() ;
  int disketteExtension__InterfaceString__Buffer = __VERIFIER_nondet_int() ;
  int disketteExtension__InterfaceString = __VERIFIER_nondet_int() ;
  int disketteExtension__ArcName__Length = __VERIFIER_nondet_int() ;
  int disketteExtension__ArcName = __VERIFIER_nondet_int() ;
  int irpSp__MinorFunction = __VERIFIER_nondet_int() ;
  int IoGetConfigurationInformation__FloppyCount = __VERIFIER_nondet_int() ;
  int irpSp ;
  int disketteExtension ;
  int ntStatus ;
  int doneEvent = __VERIFIER_nondet_int() ;
  int irpSp___0 ;
  int nextIrpSp ;
  int nextIrpSp__Control ;
  int irpSp___1 ;
  int irpSp__Context ;
  int irpSp__Control ;
  long __cil_tmp29 ;
  long __cil_tmp30 ;

  {
  ntStatus = 0;
  PagingReferenceCount ++;
  if (PagingReferenceCount == 1) {

  }
  disketteExtension = DeviceObject__DeviceExtension;
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
  if (disketteExtension__IsRemoved) {
    {
    Irp__IoStatus__Information = 0;
    Irp__IoStatus__Status = -1073741738;
    myStatus = -1073741738;
    IofCompleteRequest(Irp, 0);
    }
    return (-1073741738);
  }
  if (irpSp__MinorFunction == 0) {
    goto switch_0_0;
  } else {
    if (irpSp__MinorFunction == 5) {
      goto switch_0_5;
    } else {
      if (irpSp__MinorFunction == 1) {
        goto switch_0_5;
      } else {
        if (irpSp__MinorFunction == 6) {
          goto switch_0_6;
        } else {
          if (irpSp__MinorFunction == 3) {
            goto switch_0_6;
          } else {
            if (irpSp__MinorFunction == 4) {
              goto switch_0_4;
            } else {
              if (irpSp__MinorFunction == 2) {
                goto switch_0_2;
              } else {
                goto switch_0_default;
                if (0) {
                  switch_0_0: 
                  {
                  ntStatus = FloppyStartDevice(DeviceObject, Irp);
                  }
                  goto switch_0_break;
                  switch_0_5: 
                  if (irpSp__MinorFunction == 5) {

                  }
                  if (! disketteExtension__IsStarted) {
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
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
                    return (ntStatus);
                  }
                  {
                  disketteExtension__HoldNewRequests = 1;
                  ntStatus = FlQueueIrpToThread(Irp, disketteExtension);
                  }
                  {
                  __cil_tmp29 = (long )ntStatus;
                  if (__cil_tmp29 == 259L) {
                    {
                    KeWaitForSingleObject(disketteExtension__FloppyThread, Executive,
                                          KernelMode, 0, 0);
                    }
                    if (disketteExtension__FloppyThread != 0) {

                    }
                    disketteExtension__FloppyThread = 0;
                    Irp__IoStatus__Status = 0;
                    myStatus = 0;
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
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
                  } else {
                    {
                    ntStatus = -1073741823;
                    Irp__IoStatus__Status = ntStatus;
                    myStatus = ntStatus;
                    Irp__IoStatus__Information = 0;
                    IofCompleteRequest(Irp, 0);
                    }
                  }
                  }
                  goto switch_0_break;
                  switch_0_6: 
                  if (irpSp__MinorFunction == 6) {

                  }
                  if (! disketteExtension__IsStarted) {
                    Irp__IoStatus__Status = 0;
                    myStatus = 0;
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
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
                  } else {
                    Irp__IoStatus__Status = 0;
                    myStatus = 0;
                    irpSp___0 = Irp__Tail__Overlay__CurrentStackLocation;
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
                      }
                    }
                    {
                    irpSp___1 = Irp__Tail__Overlay__CurrentStackLocation - 1;
                    irpSp__Context = doneEvent;
                    irpSp__Control = 224;
                    ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                    }
                    {
                    __cil_tmp30 = (long )ntStatus;
                    if (__cil_tmp30 == 259L) {
                      {
                      KeWaitForSingleObject(doneEvent, Executive, KernelMode, 0, 0);
                      ntStatus = myStatus;
                      }
                    }
                    }
                    {
                    disketteExtension__HoldNewRequests = 0;
                    Irp__IoStatus__Status = ntStatus;
                    myStatus = ntStatus;
                    Irp__IoStatus__Information = 0;
                    IofCompleteRequest(Irp, 0);
                    }
                  }
                  goto switch_0_break;
                  switch_0_4: 
                  disketteExtension__IsStarted = 0;
                  Irp__IoStatus__Status = 0;
                  myStatus = 0;
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
                  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                  }
                  goto switch_0_break;
                  switch_0_2: 
                  disketteExtension__HoldNewRequests = 0;
                  disketteExtension__IsStarted = 0;
                  disketteExtension__IsRemoved = 1;
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
                  Irp__IoStatus__Status = 0;
                  myStatus = 0;
                  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                  }
                  if (disketteExtension__InterfaceString__Buffer != 0) {
                    {
                    IoSetDeviceInterfaceState(disketteExtension__InterfaceString,
                                              0);
                    }
                  }
                  if (disketteExtension__ArcName__Length != 0) {
                    {
                    IoDeleteSymbolicLink(disketteExtension__ArcName);
                    }
                  }
                  IoGetConfigurationInformation__FloppyCount --;
                  goto switch_0_break;
                  switch_0_default: ;
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
                  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
                  }
                } else {
                  switch_0_break: ;
                }
              }
            }
          }
        }
      }
    }
  }
  PagingReferenceCount --;
  if (PagingReferenceCount == 0) {

  }
  return (ntStatus);
}
}
int FloppyStartDevice(int DeviceObject , int Irp ) 
{ int DeviceObject__DeviceExtension = __VERIFIER_nondet_int() ;
  int Irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int Irp__IoStatus__Status ;
  int disketteExtension__TargetObject = __VERIFIER_nondet_int() ;
  int disketteExtension__MaxTransferSize ;
  int disketteExtension__DriveType = __VERIFIER_nondet_int() ;
  int disketteExtension__PerpendicularMode ;
  int disketteExtension__DeviceUnit ;
  int disketteExtension__DriveOnValue ;
  int disketteExtension__UnderlyingPDO = __VERIFIER_nondet_int() ;
  int disketteExtension__InterfaceString = __VERIFIER_nondet_int() ;
  int disketteExtension__IsStarted ;
  int disketteExtension__HoldNewRequests ;
  int ntStatus ;
  int pnpStatus ;
  int doneEvent = __VERIFIER_nondet_int() ;
  int fdcInfo = __VERIFIER_nondet_int() ;
  int fdcInfo__BufferCount ;
  int fdcInfo__BufferSize ;
  int fdcInfo__MaxTransferSize = __VERIFIER_nondet_int() ;
  int fdcInfo__AcpiBios = __VERIFIER_nondet_int() ;
  int fdcInfo__AcpiFdiSupported = __VERIFIER_nondet_int() ;
  int fdcInfo__PeripheralNumber = __VERIFIER_nondet_int() ;
  int fdcInfo__BusType ;
  int fdcInfo__ControllerNumber = __VERIFIER_nondet_int() ;
  int fdcInfo__UnitNumber = __VERIFIER_nondet_int() ;
  int fdcInfo__BusNumber = __VERIFIER_nondet_int() ;
  int Dc ;
  int Fp ;
  int disketteExtension ;
  int irpSp ;
  int irpSp___0 ;
  int nextIrpSp ;
  int nextIrpSp__Control ;
  int irpSp___1 ;
  int irpSp__Control ;
  int irpSp__Context ;
  int InterfaceType ;
  int KUSER_SHARED_DATA__AlternativeArchitecture_NEC98x86 = __VERIFIER_nondet_int() ;
  long __cil_tmp42 ;
  int __cil_tmp43 ;
  int __cil_tmp44 ;
  int __cil_tmp45 ;
  int __cil_tmp46 ;
  int __cil_tmp47 ;
  int __cil_tmp48 ;
  int __cil_tmp49 ;

  {
  Dc = DiskController;
  Fp = FloppyDiskPeripheral;
  disketteExtension = DeviceObject__DeviceExtension;
  irpSp = Irp__Tail__Overlay__CurrentStackLocation;
  irpSp___0 = Irp__Tail__Overlay__CurrentStackLocation;
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
    }
  }
  {
  irpSp___1 = Irp__Tail__Overlay__CurrentStackLocation - 1;
  irpSp__Context = doneEvent;
  irpSp__Control = 224;
  ntStatus = IofCallDriver(disketteExtension__TargetObject, Irp);
  }
  {
  __cil_tmp42 = (long )ntStatus;
  if (__cil_tmp42 == 259L) {
    {
    ntStatus = KeWaitForSingleObject(doneEvent, Executive, KernelMode, 0, 0);
    ntStatus = myStatus;
    }
  }
  }
  {
  fdcInfo__BufferCount = 0;
  fdcInfo__BufferSize = 0;
  __cil_tmp43 = 3080;
  __cil_tmp44 = 458752;
  __cil_tmp45 = 461832;
  __cil_tmp46 = 461835;
  ntStatus = FlFdcDeviceIo(disketteExtension__TargetObject, __cil_tmp46, fdcInfo);
  }
  if (ntStatus >= 0) {
    disketteExtension__MaxTransferSize = fdcInfo__MaxTransferSize;
    if (fdcInfo__AcpiBios) {
      if (fdcInfo__AcpiFdiSupported) {
        {
        ntStatus = FlAcpiConfigureFloppy(disketteExtension, fdcInfo);
        }
        if (disketteExtension__DriveType == 4) {
          //__cil_tmp47 = uninf1();
          //disketteExtension__PerpendicularMode |= __cil_tmp47;
        }
      } else {
        goto _L;
      }
    } else {
      _L: 
      if (disketteExtension__DriveType == 4) {
        //__cil_tmp48 = uninf1();
        //disketteExtension__PerpendicularMode |= __cil_tmp48;
      }
      InterfaceType = 0;
      {
      while (1) {
        while_0_continue: /* CIL Label */ ;

        if (InterfaceType >= MaximumInterfaceType) {
          goto while_1_break;
        }
        {
        fdcInfo__BusType = InterfaceType;
        ntStatus = IoQueryDeviceDescription(fdcInfo__BusType, fdcInfo__BusNumber,
                                            Dc, fdcInfo__ControllerNumber, Fp, fdcInfo__PeripheralNumber,
                                            FlConfigCallBack, disketteExtension);
        }
        if (ntStatus >= 0) {
          goto while_1_break;
        }
        InterfaceType ++;
      }
      while_0_break: /* CIL Label */ ;
      }
      while_1_break: ;
    }
    if (ntStatus >= 0) {
      if (KUSER_SHARED_DATA__AlternativeArchitecture_NEC98x86 != 0) {
        disketteExtension__DeviceUnit = fdcInfo__UnitNumber;
        //disketteExtension__DriveOnValue = fdcInfo__UnitNumber;
      } else {
        disketteExtension__DeviceUnit = fdcInfo__PeripheralNumber;
        //__cil_tmp49 = 16 << fdcInfo__PeripheralNumber;
        //disketteExtension__DriveOnValue = fdcInfo__PeripheralNumber | __cil_tmp49;
      }
      {
      pnpStatus = IoRegisterDeviceInterface(disketteExtension__UnderlyingPDO, MOUNTDEV_MOUNTED_DEVICE_GUID,
                                            0, disketteExtension__InterfaceString);
      }
      if (pnpStatus >= 0) {
        {
        pnpStatus = IoSetDeviceInterfaceState(disketteExtension__InterfaceString,
                                              1);
        }
      }
      disketteExtension__IsStarted = 1;
      disketteExtension__HoldNewRequests = 0;
    }
  }
  {
  Irp__IoStatus__Status = ntStatus;
  myStatus = ntStatus;
  IofCompleteRequest(Irp, 0);
  }
  return (ntStatus);
}
}
int FloppyPnpComplete(int DeviceObject , int Irp , int Context ) 
{ 

  {
  {
  KeSetEvent(Context, 1, 0);
  }
  return (-1073741802);
}
}
int FlFdcDeviceIo(int DeviceObject , int Ioctl , int Data ) 
{ int ntStatus ;
  int irp ;
  int irpStack ;
  int doneEvent = __VERIFIER_nondet_int() ;
  int ioStatus = __VERIFIER_nondet_int() ;
  int irp__Tail__Overlay__CurrentStackLocation = __VERIFIER_nondet_int() ;
  int irpStack__Parameters__DeviceIoControl__Type3InputBuffer ;
  long __cil_tmp11 ;

  {
  {
  irp = IoBuildDeviceIoControlRequest(Ioctl, DeviceObject, 0, 0, 0, 0, 1, doneEvent,
                                      ioStatus);
  }
  if (irp == 0) {
    return (-1073741670);
  }
  {
  irpStack = irp__Tail__Overlay__CurrentStackLocation - 1;
  irpStack__Parameters__DeviceIoControl__Type3InputBuffer = Data;
  ntStatus = IofCallDriver(DeviceObject, irp);
  }
  {
  __cil_tmp11 = (long )ntStatus;
  if (__cil_tmp11 == 259L) {
    {
    KeWaitForSingleObject(doneEvent, Suspended, KernelMode, 0, 0);
    ntStatus = myStatus;
    }
  }
  }
  return (ntStatus);
}
}
void FloppyProcessQueuedRequests(int DisketteExtension ) 
{ 

  {
  return;
}
}
void stub_driver_init(void) 
{ 

  {
  s = NP;
  pended = 0;
  compRegistered = 0;
  lowerDriverReturn = 0;
  setEventCalled = 0;
  customIrp = 0;
  return;
}
}
int main(void) 
{ int status ;
  int irp = __VERIFIER_nondet_int() ;
  int pirp ;
  int pirp__IoStatus__Status ;
  int irp_choice = __VERIFIER_nondet_int() ;
  int devobj = __VERIFIER_nondet_int() ;
  int __cil_tmp8 ;

 FloppyThread  = 0;
 KernelMode  = 0;
 Suspended  = 0;
 Executive  = 0;
 DiskController  = 0;
 FloppyDiskPeripheral  = 0;
 FlConfigCallBack  = 0;
 MaximumInterfaceType  = 0;
 MOUNTDEV_MOUNTED_DEVICE_GUID  = 0;
 myStatus  = 0;
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
 compRegistered  = 0;
 lowerDriverReturn  = 0;
 setEventCalled  = 0;
 customIrp  = 0;

  {
  {
  status = 0;
  pirp = irp;
  _BLAST_init();
  }
  if (status >= 0) {
    s = NP;
    customIrp = 0;
    setEventCalled = customIrp;
    lowerDriverReturn = setEventCalled;
    compRegistered = lowerDriverReturn;
    pended = compRegistered;
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
    if (tmp_ndt_1 == 3) {
      goto switch_2_3;
    } else {
      goto switch_2_default;
      if (0) {
        switch_2_3: 
        {
        status = FloppyPnp(devobj, pirp);
        }
        goto switch_2_break;
        switch_2_default: ;
        return (-1);
      } else {
        switch_2_break: ;
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
                errorFn();
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
  status = 0;
  return (status);
}
}
int IoBuildDeviceIoControlRequest(int IoControlCode , int DeviceObject , int InputBuffer ,
                                  int InputBufferLength , int OutputBuffer , int OutputBufferLength ,
                                  int InternalDeviceIoControl , int Event , int IoStatusBlock ) 
{
  int malloc = __VERIFIER_nondet_int() ;

  {
  customIrp = 1;
  int tmp_ndt_2;
  tmp_ndt_2 = __VERIFIER_nondet_int();
  if (tmp_ndt_2 == 0) {
    goto switch_3_0;
  } else {
    goto switch_3_default;
    if (0) {
      switch_3_0: 
      return (malloc);
      switch_3_default: ;
      return (0);
    } else {

    }
  }
}
}
int IoDeleteSymbolicLink(int SymbolicLinkName ) 
{

  {
  int tmp_ndt_3;
  tmp_ndt_3 = __VERIFIER_nondet_int();
  if (tmp_ndt_3 == 0) {
    goto switch_4_0;
  } else {
    goto switch_4_default;
    if (0) {
      switch_4_0: 
      return (0);
      switch_4_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
int IoQueryDeviceDescription(int BusType , int BusNumber , int ControllerType , int ControllerNumber ,
                             int PeripheralType , int PeripheralNumber , int CalloutRoutine ,
                             int Context ) 
{

  {
  int tmp_ndt_4;
  tmp_ndt_4 = __VERIFIER_nondet_int();
  if (tmp_ndt_4 == 0) {
    goto switch_5_0;
  } else {
    goto switch_5_default;
    if (0) {
      switch_5_0: 
      return (0);
      switch_5_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
int IoRegisterDeviceInterface(int PhysicalDeviceObject , int InterfaceClassGuid ,
                              int ReferenceString , int SymbolicLinkName ) 
{

  {
  int tmp_ndt_5;
  tmp_ndt_5 = __VERIFIER_nondet_int();
  if (tmp_ndt_5 == 0) {
    goto switch_6_0;
  } else {
    goto switch_6_default;
    if (0) {
      switch_6_0: 
      return (0);
      switch_6_default: ;
      return (-1073741808);
    } else {

    }
  }
}
}
int IoSetDeviceInterfaceState(int SymbolicLinkName , int Enable ) 
{

  {
  int tmp_ndt_6;
  tmp_ndt_6 = __VERIFIER_nondet_int();
  if (tmp_ndt_6 == 0) {
    goto switch_7_0;
  } else {
    goto switch_7_default;
    if (0) {
      switch_7_0: 
      return (0);
      switch_7_default: ;
      return (-1073741823);
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
  int compRetStatus1 ;
  int lcontext = __VERIFIER_nondet_int() ;
  unsigned long __cil_tmp7 ;

  {
  if (compRegistered) {
    {
    compRetStatus1 = FloppyPnpComplete(DeviceObject, Irp, lcontext);
    }
    {
    __cil_tmp7 = (unsigned long )compRetStatus1;
    if (__cil_tmp7 == -1073741802) {
      {
      stubMoreProcessingRequired();
      }
    }
    }
  }
  int tmp_ndt_12;
  tmp_ndt_12 = __VERIFIER_nondet_int();
  if (tmp_ndt_12 == 0) {
    goto switch_8_0;
  } else {
    int tmp_ndt_7;
    tmp_ndt_7 = __VERIFIER_nondet_int();
    if (tmp_ndt_7 == 1) {
      goto switch_8_1;
    } else {
      goto switch_8_default;
      if (0) {
        switch_8_0: 
        returnVal2 = 0;
        goto switch_8_break;
        switch_8_1: 
        returnVal2 = -1073741823;
        goto switch_8_break;
        switch_8_default: 
        returnVal2 = 259;
        goto switch_8_break;
      } else {
        switch_8_break: ;
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
  int tmp_ndt_8;
  tmp_ndt_8 = __VERIFIER_nondet_int();
  if (tmp_ndt_8 == 0) {
    goto switch_9_0;
  } else {
    goto switch_9_default;
    if (0) {
      switch_9_0: 
      return (0);
      switch_9_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
int ObReferenceObjectByHandle(int Handle , int DesiredAccess , int ObjectType , int AccessMode ,
                              int Object , int HandleInformation ) 
{

  {
  int tmp_ndt_9;
  tmp_ndt_9 = __VERIFIER_nondet_int();
  if (tmp_ndt_9 == 0) {
    goto switch_10_0;
  } else {
    goto switch_10_default;
    if (0) {
      switch_10_0: 
      return (0);
      switch_10_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
int PsCreateSystemThread(int ThreadHandle , int DesiredAccess , int ObjectAttributes ,
                         int ProcessHandle , int ClientId , int StartRoutine , int StartContext ) 
{

  {
  int tmp_ndt_10;
  tmp_ndt_10 = __VERIFIER_nondet_int();
  if (tmp_ndt_10 == 0) {
    goto switch_11_0;
  } else {
    goto switch_11_default;
    if (0) {
      switch_11_0: 
      return (0);
      switch_11_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
int ZwClose(int Handle ) 
{

  {
  int tmp_ndt_11;
  tmp_ndt_11 = __VERIFIER_nondet_int();
  if (tmp_ndt_11 == 0) {
    goto switch_12_0;
  } else {
    goto switch_12_default;
    if (0) {
      switch_12_0: 
      return (0);
      switch_12_default: ;
      return (-1073741823);
    } else {

    }
  }
}
}
