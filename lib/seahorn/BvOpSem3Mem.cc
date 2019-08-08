/**
   Memory related functions from Bv2OpSem.
   Adapted from llvm::ExecutionEngine
 */

#include "seahorn/BvOpSem2.hh"
#include "seahorn/Support/SeaDebug.h"
#include "seahorn/Support/SeaLog.hh"


using namespace llvm;
namespace {
/// from: llvm/lib/ExecutionEngine/ExecutionEngine.cpp
/// StoreIntToMemory - Fills the StoreBytes bytes of memory starting from Dst
/// with the integer held in IntVal.
static void StoreIntToMemory(const APInt &IntVal, uint8_t *Dst,
                             unsigned StoreBytes) {
  assert((IntVal.getBitWidth() + 7) / 8 >= StoreBytes && "Integer too small!");
  const uint8_t *Src = (const uint8_t *)IntVal.getRawData();

  if (sys::IsLittleEndianHost) {
    // Little-endian host - the source is ordered from LSB to MSB.  Order the
    // destination from LSB to MSB: Do a straight copy.
    memcpy(Dst, Src, StoreBytes);
  } else {
    // Big-endian host - the source is an array of 64 bit words ordered from
    // LSW to MSW.  Each word is ordered from MSB to LSB.  Order the destination
    // from MSB to LSB: Reverse the word order, but not the bytes in a word.
    while (StoreBytes > sizeof(uint64_t)) {
      StoreBytes -= sizeof(uint64_t);
      // May not be aligned so use memcpy.
      memcpy(Dst + StoreBytes, Src, sizeof(uint64_t));
      Src += sizeof(uint64_t);
    }

    memcpy(Dst, Src + sizeof(uint64_t) - StoreBytes, StoreBytes);
  }
}

} // namespace
namespace seahorn {
/// from: llvm/lib/ExecutionEngine/ExecutionEngine.cpp
void Bv2OpSem::storeValueToMemory(const GenericValue &Val, GenericValue *Ptr,
                                  Type *Ty) {
  const unsigned StoreBytes = getDataLayout().getTypeStoreSize(Ty);

  switch (Ty->getTypeID()) {
  default:
    dbgs() << "Cannot store value of type " << *Ty << "!\n";
    break;
  case Type::IntegerTyID:
    StoreIntToMemory(Val.IntVal, (uint8_t *)Ptr, StoreBytes);
    break;
  case Type::FloatTyID:
    *((float *)Ptr) = Val.FloatVal;
    break;
  case Type::DoubleTyID:
    *((double *)Ptr) = Val.DoubleVal;
    break;
  case Type::X86_FP80TyID:
    memcpy(Ptr, Val.IntVal.getRawData(), 10);
    break;
  case Type::PointerTyID:
    // Ensure 64 bit target pointers are fully initialized on 32 bit hosts.
    if (StoreBytes != sizeof(PointerTy))
      memset(&(Ptr->PointerVal), 0, StoreBytes);

    *((PointerTy *)Ptr) = Val.PointerVal;
    break;
  case Type::VectorTyID:
    for (unsigned i = 0; i < Val.AggregateVal.size(); ++i) {
      if (cast<VectorType>(Ty)->getElementType()->isDoubleTy())
        *(((double *)Ptr) + i) = Val.AggregateVal[i].DoubleVal;
      if (cast<VectorType>(Ty)->getElementType()->isFloatTy())
        *(((float *)Ptr) + i) = Val.AggregateVal[i].FloatVal;
      if (cast<VectorType>(Ty)->getElementType()->isIntegerTy()) {
        unsigned numOfBytes =
            (Val.AggregateVal[i].IntVal.getBitWidth() + 7) / 8;
        StoreIntToMemory(Val.AggregateVal[i].IntVal,
                         (uint8_t *)Ptr + numOfBytes * i, numOfBytes);
      }
    }
    break;
  }

  if (sys::IsLittleEndianHost != getDataLayout().isLittleEndian())
    // Host and target are different endian - reverse the stored bytes.
    std::reverse((uint8_t *)Ptr, StoreBytes + (uint8_t *)Ptr);
}

/// from: llvm/lib/ExecutionEngine/ExecutionEngine.cpp
void Bv2OpSem::initMemory(const Constant *Init, void *Addr) {
  // LOG("opsem", errs() << "Initializing constant:\n"; Init->dump(););

  if (isa<UndefValue>(Init))
    return;

  if (const ConstantVector *CP = dyn_cast<ConstantVector>(Init)) {
    unsigned ElementSize =
        getDataLayout().getTypeAllocSize(CP->getType()->getElementType());
    for (unsigned i = 0, e = CP->getNumOperands(); i != e; ++i)
      initMemory(CP->getOperand(i), (char *)Addr + i * ElementSize);
    return;
  }

  if (isa<ConstantAggregateZero>(Init)) {
    memset(Addr, 0, (size_t)getDataLayout().getTypeAllocSize(Init->getType()));
    return;
  }

  if (const ConstantArray *CPA = dyn_cast<ConstantArray>(Init)) {
    unsigned ElementSize =
        getDataLayout().getTypeAllocSize(CPA->getType()->getElementType());
    for (unsigned i = 0, e = CPA->getNumOperands(); i != e; ++i)
      initMemory(CPA->getOperand(i), (char *)Addr + i * ElementSize);
    return;
  }

  if (const ConstantStruct *CPS = dyn_cast<ConstantStruct>(Init)) {
    const StructLayout *SL =
        getDataLayout().getStructLayout(cast<StructType>(CPS->getType()));
    for (unsigned i = 0, e = CPS->getNumOperands(); i != e; ++i)
      initMemory(CPS->getOperand(i),
                       (char *)Addr + SL->getElementOffset(i));
    return;
  }

  if (const ConstantDataSequential *CDS =
          dyn_cast<ConstantDataSequential>(Init)) {
    // CDS is already laid out in host memory order.
    StringRef Data = CDS->getRawDataValues();
    memcpy(Addr, Data.data(), Data.size());
    return;
  }

  if (Init->getType()->isFirstClassType()) {
    auto valo = getConstantValue(Init);
    if (valo)
      storeValueToMemory(valo.getValue(), (GenericValue *)Addr, Init->getType());
    return;
  }

  ERR << "Bad Type: " << *Init->getType();
  llvm_unreachable("Unknown constant type to initialize memory with!");
}

} // namespace seahorn
